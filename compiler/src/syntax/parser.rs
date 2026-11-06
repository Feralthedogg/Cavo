use super::{
    ast::*,
    token::{Keyword as K, Token, TokenKind as T},
};
use crate::{
    diagnostic::{Diagnostic, report},
    source::{FileId, Span},
    symbol::Interner,
};

type Parsed<V> = Result<V, ()>;

pub fn parse(
    file: FileId,
    tokens: &[Token],
    symbols: &Interner,
    ast: &mut Ast,
    diagnostics: &mut Vec<Diagnostic>,
) {
    Parser {
        file,
        tokens,
        symbols,
        position: 0,
        pending: None,
        previous: tokens[0].span,
        ast,
        diagnostics,
        depth: 0,
    }
    .module();
}

#[derive(Clone, Copy)]
struct Mode {
    contract: bool,
    record: bool,
    stop_try: bool,
}
impl Mode {
    const NORMAL: Self = Self {
        contract: false,
        record: true,
        stop_try: false,
    };
    const CONTRACT: Self = Self {
        contract: true,
        ..Self::NORMAL
    };
}

struct Parser<'a> {
    file: FileId,
    tokens: &'a [Token],
    symbols: &'a Interner,
    position: usize,
    pending: Option<Token>,
    previous: Span,
    ast: &'a mut Ast,
    diagnostics: &'a mut Vec<Diagnostic>,
    depth: usize,
}

impl Parser<'_> {
    fn current(&self) -> Token {
        self.pending.unwrap_or(self.tokens[self.position])
    }
    fn at(&self, kind: T) -> bool {
        self.current().kind == kind
    }
    fn kw(&self, keyword: K) -> bool {
        self.at(T::Keyword(keyword))
    }
    fn peek(&self, distance: usize) -> T {
        if self.pending.is_some() {
            if distance == 0 {
                return self.current().kind;
            }
            return self
                .tokens
                .get(self.position + distance - 1)
                .map_or(T::Eof, |t| t.kind);
        }
        self.tokens
            .get(self.position + distance)
            .map_or(T::Eof, |t| t.kind)
    }
    fn bump(&mut self) -> Token {
        let token = self.current();
        if self.pending.take().is_none() && token.kind != T::Eof {
            self.position += 1;
        }
        self.previous = token.span;
        token
    }
    fn eat(&mut self, kind: T) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn eat_kw(&mut self, keyword: K) -> bool {
        self.eat(T::Keyword(keyword))
    }
    fn eat_reference(&mut self) -> bool {
        if self.eat(T::Amp) {
            return true;
        }
        if self.at(T::AmpAmp) {
            let token = self.bump();
            let middle = token.span.start + 1;
            self.previous = Span::new(token.span.file, token.span.start, middle);
            self.pending = Some(Token {
                kind: T::Amp,
                span: Span::new(token.span.file, middle, token.span.end),
            });
            return true;
        }
        false
    }
    fn expect(&mut self, kind: T) -> Parsed<Token> {
        if self.at(kind) {
            Ok(self.bump())
        } else {
            let found = self.current();
            let mut diagnostic = Diagnostic::error(
                "E-PARSE-001",
                format!("expected {kind}, found {}", found.kind),
                found.span,
            );
            if kind == T::Semicolon {
                diagnostic.primary = Span::new(self.file, self.previous.end, self.previous.end);
                diagnostic = diagnostic
                    .primary_label("expected `;` here")
                    .help("add `;` to finish this statement");
            }
            report(self.diagnostics, diagnostic);
            Err(())
        }
    }
    fn error(&mut self, code: &'static str, message: impl Into<String>) {
        report(
            self.diagnostics,
            Diagnostic::error(code, message, self.current().span),
        );
    }
    fn name(&mut self) -> Parsed<Name> {
        if let T::Ident(symbol) = self.current().kind {
            Ok(Name {
                symbol,
                span: self.bump().span,
            })
        } else {
            self.error("E-PARSE-001", "expected an identifier");
            Err(())
        }
    }
    fn path(&mut self) -> Parsed<Vec<Name>> {
        let mut path = vec![self.name()?];
        while self.at(T::ColonColon) && matches!(self.peek(1), T::Ident(_)) {
            self.bump();
            path.push(self.name()?);
        }
        Ok(path)
    }
    fn span_from(&self, start: Span) -> Span {
        start.join(self.previous)
    }
    fn enter(&mut self) -> Parsed<()> {
        if self.depth >= 128 {
            self.error("E-PARSE-DEPTH", "syntax nesting exceeds 128 levels");
            Err(())
        } else {
            self.depth += 1;
            Ok(())
        }
    }

    fn module(&mut self) {
        let mut name = Vec::new();
        let mut imports = Vec::new();
        let mut items = Vec::new();
        if self.eat_kw(K::Module) {
            match self.declaration_path().and_then(|path| {
                self.expect(T::Semicolon)?;
                Ok(path)
            }) {
                Ok(path) => name = path,
                Err(()) => self.recover(false),
            }
        }
        while !self.at(T::Eof) {
            let position = (self.position, self.pending);
            if self.eat_kw(K::Import) {
                let start = self.previous;
                match self.declaration_path().and_then(|path| {
                    self.expect(T::Semicolon)?;
                    Ok(path)
                }) {
                    Ok(path) => imports.push(Import {
                        path,
                        span: self.span_from(start),
                    }),
                    Err(()) => self.recover(false),
                }
            } else {
                match self.item() {
                    Ok(item) => items.push(item),
                    Err(()) => self.recover(false),
                }
            }
            if position == (self.position, self.pending) {
                self.bump();
            }
        }
        self.ast.modules.push(Module {
            file: self.file,
            name,
            imports,
            items,
        });
    }

    fn declaration_path(&mut self) -> Parsed<Vec<Name>> {
        let path = self.path()?;
        if self.at(T::Dot) {
            self.error("E-PARSE-PATH", "module and import paths use '::', not '.'");
            return Err(());
        }
        Ok(path)
    }

    fn recover(&mut self, inside: bool) {
        let mut depth = 0_usize;
        while !self.at(T::Eof) {
            if depth == 0 {
                if self.eat(T::Semicolon) {
                    return;
                }
                if self.at(T::RightBrace) {
                    if !inside {
                        self.bump();
                    }
                    return;
                }
            }
            match self.bump().kind {
                T::LeftBrace => depth += 1,
                T::RightBrace => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return;
                    }
                }
                _ => {}
            }
        }
    }

    fn attributes(&mut self) -> Parsed<Vec<Attribute>> {
        let mut attributes = Vec::new();
        while self.eat(T::At) {
            let start = self.previous;
            let name = self.name()?;
            let mut arguments = Vec::new();
            let mut expression = None;
            if self.eat(T::LeftParen) {
                if self.symbols.get(name.symbol) == "align" {
                    let begin = self.position;
                    expression = Some(self.expression()?);
                    arguments.extend_from_slice(&self.tokens[begin..self.position]);
                    self.expect(T::RightParen)?;
                } else {
                    arguments = self.attribute_tokens()?;
                }
            }
            attributes.push(Attribute {
                name,
                arguments,
                expression,
                span: self.span_from(start),
            });
        }
        Ok(attributes)
    }

    fn attribute_tokens(&mut self) -> Parsed<Vec<Token>> {
        let mut arguments = Vec::new();
        let mut closers = vec![T::RightParen];
        while !closers.is_empty() && !self.at(T::Eof) {
            let token = self.bump();
            match token.kind {
                T::LeftParen => closers.push(T::RightParen),
                T::LeftBrace => closers.push(T::RightBrace),
                T::LeftBracket => closers.push(T::RightBracket),
                T::RightParen | T::RightBrace | T::RightBracket
                    if closers.pop() != Some(token.kind) =>
                {
                    self.error("E-PARSE-001", "mismatched attribute delimiter");
                    return Err(());
                }
                _ => {}
            }
            if !closers.is_empty() {
                arguments.push(token);
            }
        }
        if !closers.is_empty() {
            self.error("E-PARSE-001", "unterminated attribute");
            return Err(());
        }
        Ok(arguments)
    }

    fn visibility(&mut self) -> Parsed<Visibility> {
        if !self.eat_kw(K::Pub) {
            return Ok(Visibility::Private);
        }
        if self.eat(T::LeftParen) {
            self.expect(T::Keyword(K::Package))?;
            self.expect(T::RightParen)?;
            Ok(Visibility::Package)
        } else {
            Ok(Visibility::Public)
        }
    }

    fn item(&mut self) -> Parsed<ItemId> {
        let start = self.current().span;
        let attributes = self.attributes()?;
        let visibility = self.visibility()?;
        let (name, kind) = if self.eat_kw(K::StaticAssert) {
            (None, ItemKind::StaticAssert(self.static_assert(start)?))
        } else if self.eat_kw(K::Type) {
            let name = self.name()?;
            let generics = self.generics()?;
            self.expect(T::Equal)?;
            let target = self.ty()?;
            self.expect(T::Semicolon)?;
            (Some(name), ItemKind::TypeAlias { generics, target })
        } else if self.kw(K::Struct) || self.kw(K::Union) {
            let union = self.eat_kw(K::Union);
            if !union {
                self.bump();
            }
            let name = self.name()?;
            let generics = self.generics()?;
            let (fields, assertions) = self.record_fields()?;
            self.eat(T::Semicolon);
            (
                Some(name),
                ItemKind::Record {
                    union,
                    generics,
                    fields,
                    assertions,
                },
            )
        } else if self.eat_kw(K::Enum) {
            let name = self.name()?;
            let generics = self.generics()?;
            self.expect(T::LeftBrace)?;
            let mut variants = Vec::new();
            while !self.at(T::RightBrace) && !self.at(T::Eof) {
                let name = self.name()?;
                let mut fields = Vec::new();
                let mut named_fields = Vec::new();
                if self.eat(T::LeftParen) {
                    while !self.at(T::RightParen) && !self.at(T::Eof) {
                        fields.push(self.ty()?);
                        if !self.eat(T::Comma) {
                            break;
                        }
                    }
                    self.expect(T::RightParen)?;
                } else if self.at(T::LeftBrace) {
                    named_fields = self.fields()?;
                }
                let discriminant = if self.eat(T::Equal) {
                    Some(self.expression()?)
                } else {
                    None
                };
                variants.push(Variant {
                    name,
                    fields,
                    named_fields,
                    discriminant,
                });
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.expect(T::RightBrace)?;
            self.eat(T::Semicolon);
            (Some(name), ItemKind::Enum { generics, variants })
        } else if self.eat_kw(K::Trait) {
            let name = self.name()?;
            let generics = self.generics()?;
            let bounds = self.bounds()?;
            let methods = self.item_block()?;
            (
                Some(name),
                ItemKind::Trait {
                    generics,
                    bounds,
                    methods,
                },
            )
        } else if self.eat_kw(K::Impl) {
            (None, self.implementation(false)?)
        } else if self.eat_kw(K::Contract) {
            if self.eat_kw(K::Impl) {
                (None, self.implementation(true)?)
            } else {
                let name = self.name()?;
                let generics = self.generics()?;
                let (parameters, variadic) = self.parameters()?;
                if variadic {
                    self.error("E-PARSE-001", "contracts cannot be variadic");
                    return Err(());
                }
                self.expect(T::LeftBrace)?;
                let mut requirements = Vec::new();
                while self.eat_kw(K::Requires) {
                    requirements.push(self.expression_mode(Mode::CONTRACT)?);
                    self.expect(T::Semicolon)?;
                }
                self.expect(T::RightBrace)?;
                (
                    Some(name),
                    ItemKind::Contract {
                        generics,
                        parameters,
                        requirements,
                    },
                )
            }
        } else if self.eat_kw(K::Extern) {
            let token = self.expect(T::String)?;
            let abi = self
                .ast
                .add_expr(ExprKind::Literal(LiteralKind::String), token.span);
            let items = self.item_block()?;
            (None, ItemKind::Extern { abi, items })
        } else {
            let constant = self.eat_kw(K::Const);
            let result = self.ty()?;
            let name = self.name()?;
            let generics = self.generics()?;
            if self.at(T::LeftParen) {
                let (parameters, variadic) = self.parameters()?;
                let clauses = self.clauses()?;
                let body = if self.eat(T::Semicolon) {
                    None
                } else {
                    Some(self.block()?)
                };
                (
                    Some(name),
                    ItemKind::Function(Function {
                        constant,
                        generics,
                        parameters,
                        result,
                        clauses,
                        body,
                        variadic,
                    }),
                )
            } else {
                if !generics.is_empty() {
                    self.error("E-PARSE-001", "global bindings cannot be generic");
                    return Err(());
                }
                let initializer = if self.eat(T::Equal) {
                    Some(self.expression()?)
                } else {
                    None
                };
                self.expect(T::Semicolon)?;
                (
                    Some(name),
                    ItemKind::Global(Variable {
                        constant,
                        name,
                        ty: result,
                        initializer,
                    }),
                )
            }
        };
        Ok(self.ast.add_item(Item {
            name,
            visibility,
            attributes,
            kind,
            span: self.span_from(start),
        }))
    }

    fn fields(&mut self) -> Parsed<Vec<Field>> {
        let (fields, assertions) = self.record_fields()?;
        if !assertions.is_empty() {
            self.error(
                "E-PARSE-001",
                "static_assert is not allowed in a variant field list",
            );
            return Err(());
        }
        Ok(fields)
    }

    fn record_fields(&mut self) -> Parsed<(Vec<Field>, Vec<StaticAssert>)> {
        self.expect(T::LeftBrace)?;
        let mut fields = Vec::new();
        let mut assertions = Vec::new();
        while !self.at(T::RightBrace) && !self.at(T::Eof) {
            if self.kw(K::StaticAssert) {
                let start = self.bump().span;
                assertions.push(self.static_assert(start)?);
                continue;
            }
            let visibility = self.visibility()?;
            let ty = self.ty()?;
            let name = self.name()?;
            self.expect(T::Semicolon)?;
            fields.push(Field {
                name,
                ty,
                visibility,
            });
        }
        self.expect(T::RightBrace)?;
        Ok((fields, assertions))
    }

    fn static_assert(&mut self, start: Span) -> Parsed<StaticAssert> {
        self.expect(T::LeftParen)?;
        let condition = self.expression()?;
        let message = if self.eat(T::Comma) {
            let token = self.expect(T::String)?;
            Some(
                self.ast
                    .add_expr(ExprKind::Literal(LiteralKind::String), token.span),
            )
        } else {
            None
        };
        self.expect(T::RightParen)?;
        self.expect(T::Semicolon)?;
        Ok(StaticAssert {
            condition,
            message,
            span: self.span_from(start),
        })
    }

    fn item_block(&mut self) -> Parsed<Vec<ItemId>> {
        self.enter()?;
        let result = self.item_block_inner();
        self.depth -= 1;
        result
    }
    fn item_block_inner(&mut self) -> Parsed<Vec<ItemId>> {
        self.expect(T::LeftBrace)?;
        let mut items = Vec::new();
        while !self.at(T::RightBrace) && !self.at(T::Eof) {
            match self.item() {
                Ok(item) => items.push(item),
                Err(()) => self.recover(true),
            }
        }
        self.expect(T::RightBrace)?;
        Ok(items)
    }
    fn implementation(&mut self, trusted: bool) -> Parsed<ItemKind> {
        let generics = self.generics()?;
        let first = self.ty()?;
        let (trait_type, target) = if self.eat_kw(K::For) {
            (Some(first), self.ty()?)
        } else {
            (None, first)
        };
        let (trusted_reason, methods) = if trusted {
            self.expect(T::Keyword(K::Because))?;
            let token = self.expect(T::String)?;
            let reason = self
                .ast
                .add_expr(ExprKind::Literal(LiteralKind::String), token.span);
            self.expect(T::Semicolon)?;
            (Some(reason), Vec::new())
        } else {
            (None, self.item_block()?)
        };
        Ok(ItemKind::Impl {
            generics,
            trait_type,
            target,
            methods,
            trusted_reason,
        })
    }

    fn generics(&mut self) -> Parsed<Vec<GenericParam>> {
        let mut generics = Vec::new();
        if self.eat(T::Less) {
            while !self.at_gt() && !self.at(T::Eof) {
                if let T::Lifetime(symbol) = self.current().kind {
                    generics.push(GenericParam::Lifetime(Name {
                        symbol,
                        span: self.bump().span,
                    }));
                } else if self.eat_kw(K::Const) {
                    let ty = self.ty()?;
                    let name = self.name()?;
                    generics.push(GenericParam::Const { name, ty });
                } else {
                    let name = self.name()?;
                    let bounds = self.bounds()?;
                    generics.push(GenericParam::Type { name, bounds });
                }
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.close_gt()?;
        }
        Ok(generics)
    }
    fn bounds(&mut self) -> Parsed<Vec<TypeId>> {
        let mut bounds = Vec::new();
        if self.eat(T::Colon) {
            loop {
                bounds.push(self.ty()?);
                if !self.eat(T::Plus) {
                    break;
                }
            }
        }
        Ok(bounds)
    }
    fn parameters(&mut self) -> Parsed<(Vec<Parameter>, bool)> {
        self.expect(T::LeftParen)?;
        let mut parameters = Vec::new();
        let mut variadic = false;
        while !self.at(T::RightParen) && !self.at(T::Eof) {
            if self.eat(T::Ellipsis) {
                variadic = true;
                break;
            }
            let moved = self.eat_kw(K::Move);
            let ty = self.ty()?;
            let name = self.name()?;
            parameters.push(Parameter { name, ty, moved });
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RightParen)?;
        Ok((parameters, variadic))
    }
    fn clauses(&mut self) -> Parsed<Vec<Clause>> {
        let mut clauses = Vec::new();
        while self.kw(K::Requires) || self.kw(K::Ensures) {
            let kind = if self.eat_kw(K::Requires) {
                ClauseKind::Requires
            } else {
                self.bump();
                ClauseKind::Ensures
            };
            clauses.push(Clause {
                kind,
                predicate: self.expression_mode(Mode::CONTRACT)?,
            });
        }
        Ok(clauses)
    }
    fn at_gt(&self) -> bool {
        self.at(T::Greater) || self.at(T::ShiftRight)
    }
    fn close_gt(&mut self) -> Parsed<()> {
        if self.eat(T::Greater) {
            return Ok(());
        }
        if self.at(T::ShiftRight) {
            let token = self.bump();
            let middle = token.span.start + 1;
            self.previous = Span::new(self.file, token.span.start, middle);
            self.pending = Some(Token {
                kind: T::Greater,
                span: Span::new(self.file, middle, token.span.end),
            });
            return Ok(());
        }
        self.expect(T::Greater).map(|_| ())
    }
    fn type_arguments(&mut self) -> Parsed<Vec<GenericArg>> {
        self.expect(T::Less)?;
        let mut arguments = Vec::new();
        while !self.at_gt() && !self.at(T::Eof) {
            if let T::Lifetime(symbol) = self.current().kind {
                let span = self.bump().span;
                arguments.push(GenericArg::Lifetime(Name { symbol, span }));
            } else if self.at(T::Integer) {
                let token = self.bump();
                let value = self
                    .ast
                    .add_expr(ExprKind::Literal(LiteralKind::Integer), token.span);
                arguments.push(GenericArg::Const(value));
            } else {
                let ty = self.ty()?;
                let argument = match &self.ast.ty(ty).kind {
                    TypeKind::Path { path, arguments } if arguments.is_empty() => {
                        GenericArg::Path(path.clone())
                    }
                    _ => GenericArg::Type(ty),
                };
                arguments.push(argument);
            }
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.close_gt()?;
        Ok(arguments)
    }

    fn ty(&mut self) -> Parsed<TypeId> {
        self.enter()?;
        let result = self.ty_inner();
        self.depth -= 1;
        result
    }
    fn ty_inner(&mut self) -> Parsed<TypeId> {
        let start = self.current().span;
        let kind = if self.eat_reference() {
            let lifetime = if let T::Lifetime(symbol) = self.current().kind {
                Some(Name {
                    symbol,
                    span: self.bump().span,
                })
            } else {
                None
            };
            let mutable = self.eat_kw(K::Mut);
            let inner = self.ty()?;
            TypeKind::Reference {
                lifetime,
                mutable,
                inner,
            }
        } else if self.eat_kw(K::Const) {
            TypeKind::Const(self.ty()?)
        } else if self.eat_kw(K::Auto) || self.eat(T::Underscore) {
            TypeKind::Infer
        } else if self.eat(T::LeftBracket) {
            let inner = self.ty()?;
            self.expect(T::RightBracket)?;
            TypeKind::Slice(inner)
        } else if self.at(T::Keyword(K::Fn)) || self.at(T::Keyword(K::For)) {
            let mut lifetimes = Vec::new();
            if self.eat_kw(K::For) {
                self.expect(T::Less)?;
                loop {
                    let T::Lifetime(symbol) = self.current().kind else {
                        self.error(
                            "E-PARSE-REGION",
                            "expected a lifetime in the callable binder",
                        );
                        return Err(());
                    };
                    lifetimes.push(Name {
                        symbol,
                        span: self.bump().span,
                    });
                    if !self.eat(T::Comma) {
                        break;
                    }
                }
                self.close_gt()?;
            }
            self.expect(T::Keyword(K::Fn))?;
            self.expect(T::LeftParen)?;
            let mut parameters = Vec::new();
            while !self.at(T::RightParen) && !self.at(T::Eof) {
                parameters.push(self.ty()?);
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.expect(T::RightParen)?;
            self.expect(T::Arrow)?;
            let result = self.ty()?;
            TypeKind::Function {
                lifetimes,
                parameters,
                result,
                attributes: self.attributes()?,
            }
        } else if self.eat_kw(K::Dyn) {
            let mut bounds = vec![self.ty()?];
            while self.eat(T::Plus) {
                bounds.push(self.ty()?);
            }
            TypeKind::Dynamic(bounds)
        } else if matches!(self.current().kind, T::Ident(_)) {
            let path = self.path()?;
            let arguments = if self.at(T::Less) {
                self.type_arguments()?
            } else {
                Vec::new()
            };
            TypeKind::Path { path, arguments }
        } else {
            self.error("E-PARSE-001", "expected a type");
            return Err(());
        };
        let mut ty = self.ast.add_type(kind, self.span_from(start));
        while self.eat(T::LeftBracket) {
            let length = self.expression()?;
            self.expect(T::RightBracket)?;
            ty = self
                .ast
                .add_type(TypeKind::Array { inner: ty, length }, self.span_from(start));
        }
        Ok(ty)
    }

    fn block(&mut self) -> Parsed<Block> {
        self.enter()?;
        let result = self.block_inner();
        self.depth -= 1;
        result
    }
    fn block_inner(&mut self) -> Parsed<Block> {
        let start = self.expect(T::LeftBrace)?.span;
        let mut statements = Vec::new();
        while !self.at(T::RightBrace) && !self.at(T::Eof) {
            let position = (self.position, self.pending);
            match self.statement() {
                Ok(statement) => statements.push(statement),
                Err(()) => self.recover(true),
            }
            if position == (self.position, self.pending) && !self.at(T::RightBrace) {
                self.bump();
            }
        }
        self.expect(T::RightBrace)?;
        Ok(Block {
            statements,
            span: self.span_from(start),
        })
    }

    fn statement(&mut self) -> Parsed<StmtId> {
        self.enter()?;
        let result = self.statement_inner();
        self.depth -= 1;
        result
    }
    fn statement_inner(&mut self) -> Parsed<StmtId> {
        let start = self.current().span;
        let kind = if self.eat_kw(K::StaticAssert) {
            StmtKind::StaticAssert(self.static_assert(start)?)
        } else if self.at(T::LeftBrace) {
            StmtKind::Block(self.block()?)
        } else if self.eat_kw(K::Return) {
            let value = if self.at(T::Semicolon) {
                None
            } else {
                Some(self.expression()?)
            };
            self.expect(T::Semicolon)?;
            StmtKind::Return(value)
        } else if self.eat_kw(K::If) {
            return self.if_chain(start);
        } else if self.eat_kw(K::While) {
            let condition = self.condition()?;
            StmtKind::While {
                condition,
                body: self.block()?,
            }
        } else if self.kw(K::For) && self.peek(1) != T::Less && self.eat_kw(K::For) {
            self.for_statement()?
        } else if self.eat_kw(K::Scope) {
            let name = if matches!(self.current().kind, T::Ident(_)) {
                Some(self.name()?)
            } else {
                None
            };
            StmtKind::Scope {
                name,
                body: self.block()?,
            }
        } else if self.eat_kw(K::Contract) {
            StmtKind::Contract(self.block()?)
        } else if self.eat_kw(K::Defer) {
            StmtKind::Defer(self.block()?)
        } else if self.eat_kw(K::Assume) {
            let predicate = self.expression_mode(Mode::CONTRACT)?;
            self.expect(T::Keyword(K::Because))?;
            let token = self.expect(T::String)?;
            let reason = self
                .ast
                .add_expr(ExprKind::Literal(LiteralKind::String), token.span);
            self.expect(T::Semicolon)?;
            StmtKind::Assume { predicate, reason }
        } else if self.eat_kw(K::Break) {
            self.expect(T::Semicolon)?;
            StmtKind::Break
        } else if self.eat_kw(K::Continue) {
            self.expect(T::Semicolon)?;
            StmtKind::Continue
        } else if self.eat(T::Semicolon) {
            StmtKind::Empty
        } else if self.looks_like_variable() {
            let variable = self.variable()?;
            self.expect(T::Semicolon)?;
            StmtKind::Variable(variable)
        } else {
            let kind = self.expression_statement()?;
            self.expect(T::Semicolon)?;
            kind
        };
        Ok(self.ast.add_stmt(kind, self.span_from(start)))
    }
    fn condition(&mut self) -> Parsed<ExprId> {
        self.expect(T::LeftParen)?;
        let condition = self.expression()?;
        self.expect(T::RightParen)?;
        Ok(condition)
    }
    fn variable(&mut self) -> Parsed<Variable> {
        let constant = self.eat_kw(K::Const);
        let ty = self.ty()?;
        let name = self.name()?;
        let initializer = if self.eat(T::Equal) {
            Some(self.expression()?)
        } else {
            None
        };
        Ok(Variable {
            constant,
            name,
            ty,
            initializer,
        })
    }
    fn expression_statement(&mut self) -> Parsed<StmtKind> {
        let target = self.expression()?;
        let operation = match self.current().kind {
            T::Equal => Some(None),
            T::PlusEqual => Some(Some(BinaryOp::Add)),
            T::MinusEqual => Some(Some(BinaryOp::Subtract)),
            T::StarEqual => Some(Some(BinaryOp::Multiply)),
            T::SlashEqual => Some(Some(BinaryOp::Divide)),
            T::PercentEqual => Some(Some(BinaryOp::Remainder)),
            T::AmpEqual => Some(Some(BinaryOp::BitAnd)),
            T::PipeEqual => Some(Some(BinaryOp::BitOr)),
            T::CaretEqual => Some(Some(BinaryOp::BitXor)),
            T::ShiftLeftEqual => Some(Some(BinaryOp::ShiftLeft)),
            T::ShiftRightEqual => Some(Some(BinaryOp::ShiftRight)),
            _ => None,
        };
        if let Some(op) = operation {
            self.bump();
            Ok(StmtKind::Assign {
                target,
                op,
                value: self.expression()?,
            })
        } else {
            Ok(StmtKind::Expression(target))
        }
    }
    fn for_statement(&mut self) -> Parsed<StmtKind> {
        self.expect(T::LeftParen)?;
        let initialize = if self.eat(T::Semicolon) {
            None
        } else {
            let start = self.current().span;
            let kind = if self.looks_like_variable() {
                let variable = self.variable()?;
                if self.eat_kw(K::In) {
                    let iterable = self.expression()?;
                    self.expect(T::RightParen)?;
                    return Ok(StmtKind::ForIn {
                        variable,
                        iterable,
                        body: self.block()?,
                    });
                }
                StmtKind::Variable(variable)
            } else {
                self.expression_statement()?
            };
            self.expect(T::Semicolon)?;
            Some(self.ast.add_stmt(kind, self.span_from(start)))
        };
        let condition = if self.eat(T::Semicolon) {
            None
        } else {
            let condition = self.expression()?;
            self.expect(T::Semicolon)?;
            Some(condition)
        };
        let update = if self.at(T::RightParen) {
            None
        } else {
            let start = self.current().span;
            let kind = self.expression_statement()?;
            Some(self.ast.add_stmt(kind, self.span_from(start)))
        };
        self.expect(T::RightParen)?;
        Ok(StmtKind::For {
            initialize,
            condition,
            update,
            body: self.block()?,
        })
    }

    fn looks_like_variable(&self) -> bool {
        if self.kw(K::Const) || self.kw(K::Auto) {
            return true;
        }
        let Some(index) = self.skip_type(0, 0) else {
            return false;
        };
        matches!(self.peek(index), T::Ident(_))
    }
    fn if_chain(&mut self, mut start: Span) -> Parsed<StmtId> {
        let mut arms = Vec::new();
        let mut otherwise = loop {
            let condition = self.condition()?;
            let then_block = self.block()?;
            arms.push((start, condition, then_block));
            if !self.eat_kw(K::Else) {
                break None;
            }
            if self.kw(K::If) {
                start = self.bump().span;
                continue;
            }
            if !self.at(T::LeftBrace) {
                self.error("E-PARSE-001", "else requires a block or if");
                return Err(());
            }
            break Some(self.statement()?);
        };
        let end = self.previous;
        for (start, condition, then_block) in arms.into_iter().rev() {
            otherwise = Some(self.ast.add_stmt(
                StmtKind::If {
                    condition,
                    then_block,
                    otherwise,
                },
                start.join(end),
            ));
        }
        Ok(otherwise.expect("an if chain contains its first arm"))
    }
    fn skip_type(&self, mut at: usize, depth: usize) -> Option<usize> {
        if depth > 128 {
            return None;
        }
        if matches!(self.peek(at), T::Amp | T::AmpAmp) {
            let references = if self.peek(at) == T::AmpAmp { 2 } else { 1 };
            at += 1;
            if matches!(self.peek(at), T::Lifetime(_)) {
                at += 1;
            }
            if self.peek(at) == T::Keyword(K::Mut) {
                at += 1;
            }
            return self.skip_type(at, depth + references);
        }
        if self.peek(at) == T::Keyword(K::Const) {
            return self.skip_type(at + 1, depth + 1);
        }
        if self.peek(at) == T::Keyword(K::Dyn) {
            return self.skip_type(at + 1, depth + 1);
        }
        if self.peek(at) == T::Keyword(K::For) && self.peek(at + 1) == T::Less {
            at += 2;
            loop {
                if !matches!(self.peek(at), T::Lifetime(_)) {
                    return None;
                }
                at += 1;
                if self.peek(at) != T::Comma {
                    break;
                }
                at += 1;
            }
            if self.peek(at) != T::Greater {
                return None;
            }
            return self.skip_type(at + 1, depth + 1);
        }
        if self.peek(at) == T::Keyword(K::Fn) && self.peek(at + 1) == T::LeftParen {
            at = self.skip_delimited(at + 1, T::LeftParen, T::RightParen)?;
            if self.peek(at) != T::Arrow {
                return None;
            }
            return self.skip_type(at + 1, depth + 1);
        }
        if self.peek(at) == T::LeftBracket {
            let end = self.skip_delimited(at, T::LeftBracket, T::RightBracket)?;
            return Some(end);
        }
        if !matches!(self.peek(at), T::Ident(_)) {
            return None;
        }
        at += 1;
        while self.peek(at) == T::ColonColon && matches!(self.peek(at + 1), T::Ident(_)) {
            at += 2;
        }
        if self.peek(at) == T::Less {
            let mut nesting = 1_i32;
            at += 1;
            while nesting > 0 {
                match self.peek(at) {
                    T::Less => nesting += 1,
                    T::Greater => nesting -= 1,
                    T::ShiftRight => nesting -= 2,
                    T::Eof | T::Semicolon | T::LeftBrace => return None,
                    _ => {}
                }
                at += 1;
            }
            if nesting != 0 {
                return None;
            }
        }
        while self.peek(at) == T::LeftBracket {
            at = self.skip_delimited(at, T::LeftBracket, T::RightBracket)?;
        }
        Some(at)
    }
    fn skip_delimited(&self, mut at: usize, open: T, close: T) -> Option<usize> {
        let mut nesting = 0;
        loop {
            let kind = self.peek(at);
            if kind == T::Eof {
                return None;
            }
            if kind == open {
                nesting += 1;
            } else if kind == close {
                nesting -= 1;
                if nesting == 0 {
                    return Some(at + 1);
                }
            }
            at += 1;
        }
    }

    fn expression(&mut self) -> Parsed<ExprId> {
        self.expression_mode(Mode::NORMAL)
    }
    fn expression_mode(&mut self, mode: Mode) -> Parsed<ExprId> {
        self.expression_bp(0, mode)
    }
    fn expression_bp(&mut self, minimum: u8, mode: Mode) -> Parsed<ExprId> {
        self.enter()?;
        let result = self.expression_inner(minimum, mode);
        self.depth -= 1;
        result
    }
    fn expression_inner(&mut self, minimum: u8, mode: Mode) -> Parsed<ExprId> {
        let mut left = self.prefix(mode)?;
        loop {
            let start = self.ast.expr(left).span;
            if minimum <= 23 {
                if self.at(T::LeftParen) {
                    let arguments = self.arguments(mode)?;
                    left = self.ast.add_expr(
                        ExprKind::Call {
                            callee: left,
                            type_arguments: Vec::new(),
                            arguments,
                        },
                        self.span_from(start),
                    );
                    continue;
                }
                if (self.at(T::ColonColon) && self.peek(1) == T::Less)
                    || (mode.contract && self.contract_arguments_ahead())
                {
                    self.eat(T::ColonColon);
                    let type_arguments = self.type_arguments()?;
                    let arguments = self.arguments(mode)?;
                    left = self.ast.add_expr(
                        ExprKind::Call {
                            callee: left,
                            type_arguments,
                            arguments,
                        },
                        self.span_from(start),
                    );
                    continue;
                }
                if self.eat(T::Dot) {
                    let name = self.name()?;
                    left = self
                        .ast
                        .add_expr(ExprKind::Field { base: left, name }, self.span_from(start));
                    continue;
                }
                if self.eat(T::LeftBracket) {
                    let index = self.expression()?;
                    self.expect(T::RightBracket)?;
                    left = self
                        .ast
                        .add_expr(ExprKind::Index { base: left, index }, self.span_from(start));
                    continue;
                }
                if !mode.stop_try && self.eat(T::Question) {
                    left = self
                        .ast
                        .add_expr(ExprKind::Try(left), self.span_from(start));
                    continue;
                }
            }
            let Some((power, op)) = binary(self.current().kind) else {
                break;
            };
            if power < minimum {
                break;
            }
            if comparison(op)
                && matches!(self.ast.expr(left).kind, ExprKind::Binary { op: previous, .. } if comparison(previous))
            {
                self.error(
                    "E-PARSE-CHAIN",
                    "comparison chains require explicit grouping or &&",
                );
                return Err(());
            }
            self.bump();
            let right = self.expression_bp(power + 1, mode)?;
            if comparison(op)
                && matches!(self.ast.expr(right).kind, ExprKind::Binary { op: following, .. } if comparison(following))
            {
                self.error(
                    "E-PARSE-CHAIN",
                    "comparison chains require explicit grouping or &&",
                );
                return Err(());
            }
            left = self.ast.add_expr(
                ExprKind::Binary { op, left, right },
                start.join(self.ast.expr(right).span),
            );
        }
        Ok(left)
    }
    fn prefix(&mut self, mode: Mode) -> Parsed<ExprId> {
        let token = self.current();
        let literal = match token.kind {
            T::Integer => Some(LiteralKind::Integer),
            T::Float => Some(LiteralKind::Float),
            T::String => Some(LiteralKind::String),
            T::Char => Some(LiteralKind::Char),
            T::Keyword(K::True) => Some(LiteralKind::Bool(true)),
            T::Keyword(K::False) => Some(LiteralKind::Bool(false)),
            T::Keyword(K::Null) => Some(LiteralKind::Null),
            _ => None,
        };
        if let Some(literal) = literal {
            self.bump();
            return Ok(self.ast.add_expr(ExprKind::Literal(literal), token.span));
        }
        let unary = match token.kind {
            T::Minus => Some(UnaryOp::Negate),
            T::Plus => Some(UnaryOp::Positive),
            T::Bang => Some(UnaryOp::Not),
            T::Tilde => Some(UnaryOp::BitNot),
            T::Star => Some(UnaryOp::Dereference),
            T::Amp | T::AmpAmp => Some(UnaryOp::Borrow),
            T::Keyword(K::Move) => Some(UnaryOp::Move),
            T::Keyword(K::Spawn) => Some(UnaryOp::Spawn),
            _ => None,
        };
        if let Some(mut op) = unary {
            if op == UnaryOp::Borrow {
                self.eat_reference();
            } else {
                self.bump();
            }
            if op == UnaryOp::Borrow && self.eat_kw(K::Mut) {
                op = UnaryOp::BorrowMut;
            }
            let operand = self.expression_bp(
                21,
                Mode {
                    stop_try: op == UnaryOp::Spawn || mode.stop_try,
                    ..mode
                },
            )?;
            if op == UnaryOp::Spawn && !matches!(self.ast.expr(operand).kind, ExprKind::Call { .. })
            {
                self.error("E-PARSE-SPAWN", "spawn requires a call expression");
                return Err(());
            }
            return Ok(self
                .ast
                .add_expr(ExprKind::Unary { op, operand }, self.span_from(token.span)));
        }
        match token.kind {
            T::Ident(_) => {
                let path = self.path()?;
                if mode.record && self.eat(T::LeftBrace) {
                    let mut fields = Vec::new();
                    while !self.at(T::RightBrace) && !self.at(T::Eof) {
                        let name = self.name()?;
                        self.expect(T::Colon)?;
                        fields.push((name, self.expression_mode(mode)?));
                        if !self.eat(T::Comma) {
                            break;
                        }
                    }
                    self.expect(T::RightBrace)?;
                    Ok(self.ast.add_expr(
                        ExprKind::Record { path, fields },
                        self.span_from(token.span),
                    ))
                } else {
                    Ok(self
                        .ast
                        .add_expr(ExprKind::Path(path), self.span_from(token.span)))
                }
            }
            T::LeftParen => {
                self.bump();
                let inner = self.expression_mode(Mode {
                    stop_try: false,
                    record: true,
                    ..mode
                })?;
                self.expect(T::RightParen)?;
                Ok(self
                    .ast
                    .add_expr(ExprKind::Group(inner), self.span_from(token.span)))
            }
            T::LeftBrace => {
                let body = self.block()?;
                Ok(self
                    .ast
                    .add_expr(ExprKind::Block(body), self.span_from(token.span)))
            }
            T::LeftBracket => self.array_or_closure(mode),
            T::Keyword(K::Match) => self.match_expression(mode),
            _ => {
                self.error("E-PARSE-001", "expected an expression");
                Err(())
            }
        }
    }
    fn arguments(&mut self, mode: Mode) -> Parsed<Vec<ExprId>> {
        self.expect(T::LeftParen)?;
        let mut arguments = Vec::new();
        while !self.at(T::RightParen) && !self.at(T::Eof) {
            arguments.push(self.expression_mode(Mode {
                stop_try: false,
                record: true,
                ..mode
            })?);
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RightParen)?;
        Ok(arguments)
    }
    fn contract_arguments_ahead(&self) -> bool {
        if !self.at(T::Less) {
            return false;
        }
        let mut depth = 0_i32;
        let mut at = 0;
        loop {
            match self.peek(at) {
                T::Less => depth += 1,
                T::Greater => depth -= 1,
                T::ShiftRight => depth -= 2,
                T::Eof | T::Semicolon | T::LeftBrace | T::Keyword(K::Because) => return false,
                _ => {}
            }
            at += 1;
            if depth <= 0 {
                return depth == 0 && self.peek(at) == T::LeftParen;
            }
        }
    }
    fn array_or_closure(&mut self, mode: Mode) -> Parsed<ExprId> {
        let start = self.current().span;
        let closure = self
            .skip_delimited(0, T::LeftBracket, T::RightBracket)
            .is_some_and(|end| self.peek(end) == T::LeftParen);
        self.bump();
        if closure {
            let mut captures = Vec::new();
            while !self.at(T::RightBracket) && !self.at(T::Eof) {
                let mode = if self.eat_kw(K::Move) {
                    CaptureMode::Move
                } else {
                    self.expect(T::Amp)?;
                    if self.eat_kw(K::Mut) {
                        CaptureMode::Mutable
                    } else {
                        CaptureMode::Shared
                    }
                };
                captures.push(Capture {
                    name: self.name()?,
                    mode,
                });
                if !self.eat(T::Comma) {
                    break;
                }
            }
            self.expect(T::RightBracket)?;
            let (parameters, variadic) = self.parameters()?;
            if variadic {
                self.error("E-PARSE-001", "closures cannot be variadic");
                return Err(());
            }
            let result = if self.eat(T::Arrow) {
                Some(self.ty()?)
            } else {
                None
            };
            let body = self.block()?;
            return Ok(self.ast.add_expr(
                ExprKind::Closure {
                    captures,
                    parameters,
                    result,
                    body,
                },
                self.span_from(start),
            ));
        }
        let mut elements = Vec::new();
        while !self.at(T::RightBracket) && !self.at(T::Eof) {
            elements.push(self.expression_mode(mode)?);
            if elements.len() == 1 && self.eat(T::Semicolon) {
                let count = self.expression_mode(mode)?;
                self.expect(T::RightBracket)?;
                return Ok(self.ast.add_expr(
                    ExprKind::Repeat {
                        value: elements[0],
                        count,
                    },
                    self.span_from(start),
                ));
            }
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RightBracket)?;
        Ok(self
            .ast
            .add_expr(ExprKind::Array(elements), self.span_from(start)))
    }
    fn match_expression(&mut self, mode: Mode) -> Parsed<ExprId> {
        let start = self.bump().span;
        let value = self.expression_mode(Mode {
            record: false,
            ..mode
        })?;
        self.expect(T::LeftBrace)?;
        let mut arms = Vec::new();
        while !self.at(T::RightBrace) && !self.at(T::Eof) {
            let pattern = self.pattern()?;
            let guard = if self.eat_kw(K::If) {
                Some(self.expression_mode(mode)?)
            } else {
                None
            };
            self.expect(T::FatArrow)?;
            let value = self.expression_mode(mode)?;
            arms.push(MatchArm {
                pattern,
                guard,
                value,
            });
            if !self.eat(T::Comma) {
                break;
            }
        }
        self.expect(T::RightBrace)?;
        Ok(self
            .ast
            .add_expr(ExprKind::Match { value, arms }, self.span_from(start)))
    }
    fn pattern(&mut self) -> Parsed<Pattern> {
        self.enter()?;
        let result = self.pattern_inner();
        self.depth -= 1;
        result
    }
    fn pattern_inner(&mut self) -> Parsed<Pattern> {
        let start = self.current().span;
        let kind = if self.eat(T::Underscore) {
            PatternKind::Wildcard
        } else if matches!(self.current().kind, T::Ident(_)) {
            let path = self.path()?;
            let mut fields = Vec::new();
            if self.eat(T::LeftParen) {
                while !self.at(T::RightParen) && !self.at(T::Eof) {
                    fields.push(self.pattern()?);
                    if !self.eat(T::Comma) {
                        break;
                    }
                }
                self.expect(T::RightParen)?;
            }
            PatternKind::Path { path, fields }
        } else {
            let kind = match self.current().kind {
                T::Integer => LiteralKind::Integer,
                T::Char => LiteralKind::Char,
                T::Keyword(K::True) => LiteralKind::Bool(true),
                T::Keyword(K::False) => LiteralKind::Bool(false),
                _ => {
                    self.error("E-PARSE-001", "expected a pattern");
                    return Err(());
                }
            };
            self.bump();
            PatternKind::Literal(kind)
        };
        Ok(Pattern {
            kind,
            span: self.span_from(start),
        })
    }
}

fn comparison(op: BinaryOp) -> bool {
    matches!(
        op,
        BinaryOp::Less
            | BinaryOp::LessEqual
            | BinaryOp::Greater
            | BinaryOp::GreaterEqual
            | BinaryOp::Equal
            | BinaryOp::NotEqual
    )
}
fn binary(token: T) -> Option<(u8, BinaryOp)> {
    use BinaryOp as B;
    Some(match token {
        T::PipePipe => (1, B::Or),
        T::AmpAmp => (3, B::And),
        T::Pipe => (5, B::BitOr),
        T::Caret => (7, B::BitXor),
        T::Amp => (9, B::BitAnd),
        T::EqualEqual => (11, B::Equal),
        T::BangEqual => (11, B::NotEqual),
        T::Less => (13, B::Less),
        T::LessEqual => (13, B::LessEqual),
        T::Greater => (13, B::Greater),
        T::GreaterEqual => (13, B::GreaterEqual),
        T::ShiftLeft => (15, B::ShiftLeft),
        T::ShiftRight => (15, B::ShiftRight),
        T::Plus => (17, B::Add),
        T::Minus => (17, B::Subtract),
        T::Star => (19, B::Multiply),
        T::Slash => (19, B::Divide),
        T::Percent => (19, B::Remainder),
        _ => return None,
    })
}
