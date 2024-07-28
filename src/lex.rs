use std::fmt;

#[derive(PartialEq, Debug)]
pub enum LexErrType {
    CharEmpty,
    CharsGtOne,
    InvalidChar(char),
    IntOutOfRange,

    UnexpEof,

    LinesTooMany,
    CharsTooMany,
    TotalCharsTooMany,
}

impl fmt::Display for LexErrType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LexErrType::*;
        write!(
            f,
            "{}",
            match self {
                CharEmpty => "Characters enclose exactly 1 character, found 0".to_owned(),
                CharsGtOne => "Characters enclose exactly 1 character, found multiple".to_owned(),
                InvalidChar(c) => format!("No known construct that uses symbol {}", c),
                IntOutOfRange => format!("Number found is too large"),
                UnexpEof => "End of file reached before closing of token".to_owned(),
                LinesTooMany => format!("Too many lines in this file, can only read {}", u16::MAX),
                CharsTooMany => format!(
                    "Too many characters in this line, can only read {}",
                    u16::MAX
                ),
                TotalCharsTooMany => format!(
                    "Too many characters in this file, can only read {}",
                    u32::MAX
                ),
            }
        )
    }
}

#[derive(PartialEq, Debug)]
pub struct LexErr {
    line: u16,
    character: u16,
    pub err_type: LexErrType,
}

impl LexErr {
    fn new(line: u16, character: u16, err_type: LexErrType) -> Self {
        Self {
            line,
            character,
            err_type,
        }
    }
}

impl fmt::Display for LexErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} at {}:{}", self.err_type, self.line, self.character)
    }
}

// #[derive(PartialEq, Debug)]
// pub enum FloatType {
//     //over here
//     Dot(i32, i32),
// }

#[derive(PartialEq, Debug)]
pub enum LitType {
    ///An integer token. During the tokenizing step, this will always be
    ///positive, but during evaluation passes, it may inhabit negative numbers
    Int(i32),
    Float(f64),
    Char(char),
    Str(String),
}

impl LitType {
    pub fn as_int(self) -> Result<i32, Self> {
        match self {
            LitType::Int(i) => Ok(i),
            _ => Err(self),
        }
    }
    pub fn as_float(self) -> Result<f64, Self> {
        match self {
            LitType::Float(f) => Ok(f),
            _ => Err(self),
        }
    }
    pub fn as_char(self) -> Result<char, Self> {
        match self {
            LitType::Char(c) => Ok(c),
            _ => Err(self),
        }
    }

    pub fn as_str(self) -> Result<String, Self> {
        match self {
            LitType::Str(s) => Ok(s),
            _ => Err(self),
        }
    }
}

impl fmt::Display for LitType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LitType::*;
        write!(
            f,
            "{}",
            match self {
                Int(i) => i.to_string(),
                Float(f) => format!("{}f", f),
                Char(c) => format!("'{}'", c),
                Str(s) => format!("\"{}\"", s),
            }
        )
    }
}

#[derive(PartialEq, Debug)]
pub enum OpType {
    Add,
    Sub,
    Mul,
    Div,

    IAdd,
    ISub,
    IMul,
    IDiv,

    Mod,
    Exp,
    Eq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    BAnd,
    BOr,
    Ls,
    Rs,
    Not,
}

#[derive(PartialEq, Debug)]
pub enum SymType {
    CurlyBrace(bool),
    RoundBrace(bool),
    SquareBrace(bool),
    Assoc,
    TypeSpec,
    ValSpec,
    PatternSpec,
    FuncSpec,
    Field,
    RangeSpec,
    End,
    Op(OpType),
}

impl fmt::Display for SymType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SymType::*;
        write!(
            f,
            "{}",
            match self {
                Op(op) => format!("op {:?}", op),
                _ => format!("{:?}", self),
            }
        )
    }
}

#[derive(PartialEq, Debug)]
pub enum StartType {
    Char,
    Str,
    Float(String),
}

#[derive(PartialEq, Debug)]
pub enum TokenType {
    Word(String),
    Lit(LitType),
    Sym(SymType),
    Start(StartType),
    Comment(String),
}

#[derive(PartialEq, Debug)]
pub enum TokenTypeExp {
    Word(String),
    Lit(LitType),
    Sym(SymType),
}

impl TokenTypeExp {
    pub fn as_word(self) -> Result<String, Self> {
        match self {
            TokenTypeExp::Word(w) => Ok(w),
            _ => Err(self),
        }
    }
    pub fn as_lit(self) -> Result<LitType, Self> {
        match self {
            TokenTypeExp::Lit(l) => Ok(l),
            _ => Err(self),
        }
    }
    pub fn as_sym(self) -> Result<SymType, Self> {
        match self {
            TokenTypeExp::Sym(s) => Ok(s),
            _ => Err(self),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct TokenExp {
    pub line: u16,
    pub character: u16,
    pub token_type: TokenTypeExp,
}

impl TokenExp {
    fn new(line: u16, character: u16, token_type: TokenTypeExp) -> Self {
        Self {
            line,
            character,
            token_type,
        }
    }
}

impl fmt::Display for TokenExp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenTypeExp::*;
        write!(
            f,
            "{line}:{character}\t{type}\t{content}",
            line = self.line,
            character = self.character,
            type = match self.token_type {
                Word(_) => "word",
                Lit(_) => "literal",
                Sym(_) => "symbol",
            },
            content = match self.token_type {
                Word(ref s) => s.clone(),
                Lit(ref l) => format!("{}", l),
                Sym(ref s) => format!("{}", s),
            }
        )
    }
}

#[derive(PartialEq, Debug)]
pub struct Token {
    line: u16,
    character: u16,
    pub token_type: TokenType,
}

impl Token {
    fn new(line: u16, character: u16, token_type: TokenType) -> Self {
        Self {
            line,
            character,
            token_type,
        }
    }

    fn update(self, new_token_type: TokenType) -> Self {
        Token {
            token_type: new_token_type,
            ..self
        }
    }

    fn err(self, lex_err_type: LexErrType) -> LexErr {
        LexErr {
            line: self.line,
            character: self.character,
            err_type: lex_err_type,
        }
    }

    pub fn dispatch(self, tokens: &mut Vec<TokenExp>) {
        use LitType::Float;
        use TokenType::{Lit, Start};

        assert!(
            !matches!(self.token_type, Start(StartType::Char)),
            "Start(Char) tokens mustn't be dispatched"
        );
        assert!(
            !matches!(self.token_type, Start(StartType::Str)),
            "Start(Str) tokens mustn't be dispatched"
        );

        let final_token = match self.token_type {
            TokenType::Start(StartType::Float(ref s)) => {
                let s = s.clone();
                self.update(Lit(Float(
                    str::parse(&s).expect("Start(Float) should only contain digits and period"),
                )))
            }
            _ => self,
        };

        if let Some(token_export) = final_token.export() {
            tokens.push(token_export);
        }
    }

    fn export(self) -> Option<TokenExp> {
        use TokenType::*;
        Some(TokenExp::new(
            self.line,
            self.character,
            match self.token_type {
                Word(w) => TokenTypeExp::Word(w),
                Lit(l) => TokenTypeExp::Lit(l),
                Sym(s) => TokenTypeExp::Sym(s),
                Start(_) => {
                    return None;
                }
                Comment(_) => {
                    return None;
                }
            },
        ))
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{line:<5}{character:<5}{type:<8}{content}",
            line = self.line,
            character = self.character,
            type = match self.token_type {
                TokenType::Word(_) => "word",
                TokenType::Lit(_) => "literal",
                TokenType::Sym(_) => "symbol",
                TokenType::Start(_) => "start",
                TokenType::Comment(_) => "comment",
            },
            content = match self.token_type {
                TokenType::Word(ref s) => s.clone(),
                TokenType::Lit(ref l) => format!("{}", l),
                TokenType::Sym(ref s) => format!("{}", s),
                TokenType::Start(ref st) => format!("{:?}", st),
                TokenType::Comment(ref c) => format!("\"{}\"", c),
            }
        )
    }
}

macro_rules! dispatch_and_rewind {
    ($tokens:expr, $token:expr, $line:expr, $character:expr, $counter:expr) => {{
        $token.dispatch($tokens);
        $counter -= 1;
        if $character == 0 {
            $line -= 1;
        } else {
            $character -= 1;
        }
        None
    }};
}

/// Appends characters non-special to open character/string/comment/float tokens (not `'` & `"`).

/// Returns Err(token) if the token is not of type character/string/start-character/start-string/comment,
/// otherwise returns Ok(Err([`LexErrType::CharsGtOne`])) when the token is of type character,
/// and Ok(Ok(new_token)) otherwise.
fn push_non_spec_to_char_str_or_comment(t: Token, c: char) -> Result<Result<Token, LexErr>, Token> {
    use LitType::{Char, Str};
    use TokenType::{Comment, Lit, Start};

    match t.token_type {
        Start(StartType::Char) => Ok(Ok(t.update(Lit(Char(c))))),
        Start(StartType::Str) => Ok(Ok(t.update(Lit(Str(String::from(c)))))),
        Lit(Char(_)) => Ok(Err(t.err(LexErrType::CharsGtOne))),
        Lit(Str(ref s)) => {
            let s = s.clone();
            Ok(Ok(t.update(Lit(Str(format!("{s}{c}"))))))
        }
        Comment(ref s) => {
            let s = s.clone();
            Ok(Ok(t.update(Comment(format!("{s}{c}")))))
        }
        _ => Err(t),
    }
}

pub fn lex(program: String) -> Result<Vec<TokenExp>, LexErr> {
    use LitType::{Char, Int, Str};
    use OpType::{
        Add, And, BAnd, BOr, Div, Eq, Exp, Gt, Gte, IAdd, IDiv, IMul, ISub, Ls, Lt, Lte, Mod, Mul,
        Not, Or, Rs, Sub,
    };
    use SymType::{
        Assoc, CurlyBrace, End, Field, FuncSpec, Op, PatternSpec, RangeSpec, RoundBrace,
        SquareBrace, TypeSpec, ValSpec,
    };
    use TokenType::{Comment, Lit, Start, Sym, Word};

    use LexErrType::*;

    let program = program.chars().collect::<Vec<char>>();
    let program_length = program.len();
    let mut counter = 0u32;
    let mut tokens: Vec<TokenExp> = Vec::new();
    let mut t: Option<Token> = None;

    let mut line = 1u16;
    let mut character = 1u16;

    let ts = &mut tokens;
    while (counter as usize) < program_length {
        t = if let Some(t) = t {
            match program[counter as usize] {
                //alphabet
                c @ ('a'..='z' | 'A'..='Z') => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `w` replaces token `let` with token `letw`
                        Word(ref s) => {
                            let s = s.clone();
                            Some(t.update(Word(format!("{s}{c}"))))
                        }
                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                //numbers
                c @ '0'..='9' => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `1` replaces token `var` with token `var1`
                        Word(ref s) => {
                            let s = s.clone();
                            Some(t.update(Word(format!("{s}{c}"))))
                        }

                        // `1` replaces token `34` with token `341`
                        Lit(Int(ref i)) if *i < 0 => {
                            let i = match i.checked_mul(10) {
                                Some(i) => i,
                                None => {
                                    return Err(t.err(IntOutOfRange));
                                }
                            };
                            let i = match i.checked_sub(c as i32 - '0' as i32) {
                                Some(i) => i,
                                None => {
                                    return Err(t.err(IntOutOfRange));
                                }
                            };
                            Some(t.update(Lit(Int(i))))
                        }

                        // `1` replaces token `34` with token `341`
                        Lit(Int(ref i)) if *i >= 0 => {
                            let i = match i.checked_mul(10) {
                                Some(i) => i,
                                None => {
                                    return Err(t.err(IntOutOfRange));
                                }
                            };
                            let i = match i.checked_add(c as i32 - '0' as i32) {
                                Some(i) => i,
                                None => {
                                    return Err(t.err(IntOutOfRange));
                                }
                            };
                            Some(t.update(Lit(Int(i))))
                        }

                        // `3` replaces token `.` with semi-tokem `.3`
                        Sym(Field) => Some(t.update(Start(StartType::Float(format!(".{}", c))))),

                        // `4` replaces semi-token `3.1` with semi-token `3.14`
                        Start(StartType::Float(ref s)) => {
                            let s = s.clone();
                            Some(t.update(Start(StartType::Float(format!("{s}{c}")))))
                        }

                        // Lit(Float(f)) => {
                        //    Some(t.update(Lit(Float(f * 10 + (c as i32 - '0' as i32), i + 1))))
                        //}
                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                c @ '/' => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `/` replaces token `/` with semi-token `//`
                        Sym(Op(Div)) => Some(t.update(Comment(String::new()))),

                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                c @ '=' => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `=` replaces token `+` with token `+=`
                        Sym(Op(Add)) => Some(t.update(Sym(Op(IAdd)))),
                        // `=` replaces token `-` with token `-=`
                        Sym(Op(Sub)) => Some(t.update(Sym(Op(ISub)))),
                        // `=` replaces token `*` with token `*=`
                        Sym(Op(Mul)) => Some(t.update(Sym(Op(IMul)))),
                        // `=` replaces token `/` with token `/=`
                        Sym(Op(Div)) => Some(t.update(Sym(Op(IDiv)))),

                        // `=` replaces token `=` with token `==`
                        Sym(ValSpec) => Some(t.update(Sym(Op(Eq)))),
                        // `=` replaces token `<` with token `<=`
                        Sym(Op(Lt)) => Some(t.update(Sym(Op(Lte)))),
                        // `=` replaces token `>` with token `>=`
                        Sym(Op(Gt)) => Some(t.update(Sym(Op(Gte)))),

                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                c @ '\'' => match t.token_type {
                    // `'` with semi-token `'` is a syntax-error
                    Start(StartType::Char) => {
                        return Err(t.err(CharEmpty));
                    }
                    // `'` replaces semi-token `"` with token `"'`
                    Start(StartType::Str) => Some(t.update(Lit(Str(String::from(c))))),
                    // `'` dispatches token `'c`
                    Lit(Char(_)) => {
                        t.dispatch(ts);
                        None
                    }
                    // `'` replaces token `"string` with token `"string'`
                    Lit(Str(ref s)) => {
                        let s = s.clone();
                        Some(t.update(Lit(Str(format!("{s}{c}")))))
                    }

                    _ => dispatch_and_rewind!(ts, t, line, character, counter),
                },

                c @ '"' => match t.token_type {
                    // `"` replaces semi-token `'` with token `'"`
                    Start(StartType::Char) => Some(t.update(Lit(Char(c)))),
                    // `"` dispatches token `"` (empty string)
                    Start(StartType::Str) => Some(t.update(Lit(Str(String::new())))),
                    // `"` with token `'c` is a syntax-error
                    Lit(Char(_)) => {
                        return Err(t.err(CharsGtOne));
                    }
                    // `"` dispatches token `"string`
                    Lit(Str(_)) => {
                        t.dispatch(ts);
                        None
                    }

                    _ => dispatch_and_rewind!(ts, t, line, character, counter),
                },

                c @ ':' => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `:` replaces token `:` with token `::`
                        Sym(TypeSpec) => Some(t.update(Sym(Assoc))),

                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                c @ '.' => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `.` replaces token `44` with token `44.`
                        Lit(Int(i)) => Some(t.update(Start(StartType::Float(i.to_string() + ".")))),
                        // `.` replaces token `.` with token `..`
                        Sym(Field) => Some(t.update(Sym(RangeSpec))),

                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                c @ '>' => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        // `>` relaces token `-` with token `->`
                        Sym(Op(Sub)) => Some(t.update(Sym(FuncSpec))),
                        // `>` replace token `=` with token `=>`
                        Sym(ValSpec) => Some(t.update(Sym(PatternSpec))),
                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    },
                },

                c @ '\n' => {
                    line = match line.checked_add(1) {
                        Some(line) => line,
                        None => {
                            return Err(t.err(LinesTooMany));
                        }
                    };
                    character = 0;

                    match t.token_type {
                        Start(StartType::Char) => Some(t.update(Lit(Char(c)))),
                        Start(StartType::Str) => Some(t.update(Lit(Str(String::from(c))))),
                        Lit(Char(_)) => {
                            return Err(t.err(LexErrType::CharsGtOne));
                        }
                        Lit(Str(ref s)) => {
                            let s = s.clone();
                            Some(t.update(Lit(Str(format!("{s}{c}")))))
                        }
                        Comment(_) => {
                            t.dispatch(ts);
                            None
                        }
                        _ => dispatch_and_rewind!(ts, t, line, character, counter),
                    }
                }

                // Characters not recognized by the tokenizer
                c @ _ => match push_non_spec_to_char_str_or_comment(t, c) {
                    Ok(new_t) => Some(new_t?),
                    Err(t) => match t.token_type {
                        _ => {
                            t.dispatch(ts);
                            counter -= 1;
                            if character == 0 {
                                line -= 1;
                            } else {
                                character -= 1;
                            }
                            None
                        }
                    },
                },
            }
        } else {
            match program[counter as usize] {
                // Characters start Word's, Numbers start literal Int/Float's
                c @ ('a'..='z' | 'A'..='Z') => {
                    Some(Token::new(line, character, Word(String::from(c))))
                }
                n @ '0'..='9' => Some(Token::new(line, character, Lit(Int(n as i32 - '0' as i32)))),

                // Arithmetic Operators
                '+' => Some(Token::new(line, character, Sym(Op(Add)))),
                '-' => Some(Token::new(line, character, Sym(Op(Sub)))),
                '*' => Some(Token::new(line, character, Sym(Op(Mul)))),
                '/' => Some(Token::new(line, character, Sym(Op(Div)))),
                '%' => Some(Token::new(line, character, Sym(Op(Mod)))),
                '^' => Some(Token::new(line, character, Sym(Op(Exp)))),
                '>' => Some(Token::new(line, character, Sym(Op(Lt)))),
                '<' => Some(Token::new(line, character, Sym(Op(Gt)))),
                '&' => Some(Token::new(line, character, Sym(Op(BAnd)))),
                '|' => Some(Token::new(line, character, Sym(Op(BOr)))),

                // Other Symbols
                '\'' => Some(Token::new(line, character, Start(StartType::Char))),
                '"' => Some(Token::new(line, character, Start(StartType::Str))),
                '{' => Some(Token::new(line, character, Sym(CurlyBrace(false)))),
                '}' => Some(Token::new(line, character, Sym(CurlyBrace(true)))),
                '(' => Some(Token::new(line, character, Sym(RoundBrace(false)))),
                ')' => Some(Token::new(line, character, Sym(RoundBrace(true)))),
                '[' => Some(Token::new(line, character, Sym(SquareBrace(false)))),
                ']' => Some(Token::new(line, character, Sym(SquareBrace(true)))),
                '=' => Some(Token::new(line, character, Sym(ValSpec))),
                ':' => Some(Token::new(line, character, Sym(TypeSpec))),
                '.' => Some(Token::new(line, character, Sym(Field))),
                ';' => Some(Token::new(line, character, Sym(End))),

                ' ' => None,
                '\n' => {
                    line = line //todo: if overflow, throw err: too many lines
                        .checked_add(1)
                        .ok_or(LexErr::new(line, character, LinesTooMany))?;
                    character = 0;
                    None
                }
                c @ _ => {
                    return Err(LexErr {
                        line,
                        character,
                        err_type: InvalidChar(c),
                    });
                }
            }
        };
        character = character
            .checked_add(1)
            .ok_or(LexErr::new(line, character, CharsTooMany))?;
        counter = counter
            .checked_add(1)
            .ok_or(LexErr::new(line, character, TotalCharsTooMany))?;
    }
    if let Some(token) = t {
        Err(LexErr::new(token.line, token.character, UnexpEof))
    } else {
        Ok(tokens)
    }
}

/*
TODO lex flag to not give up on failed token (maybe start again from newline)
TODO parse integers and floats simply as string, when needed transform implicitly, or use explicit markers (. or f or (int) or (float)) to transform
TODO impl ',' and '_' and comments
TODO https://learn.microsoft.com/en-us/cpp/cpp/function-call-operator-parens

NOTE the `+` + `1` = `1` logic initially put into tokenizing does not belong in this step, do it when interpreting tokens
NOTE initially, parentheses can not be used for function-calls. add this support as additional later


pub fn parse_float(num: &mut f64, base: &mut Option<f64>, ch: char) {
    if ch == '.' {
        *base = Some(0.1);
    } else {
        if let Some(base) = base {
            *num += (ch as u32 - '0' as u32) as f64 * *base;
            *base /= 10.0
        } else {
            *num *= 10.0;
            *num += (ch as u32 - '0' as u32) as f64;
        }
    }
}

pub fn parse(s: &str) -> f64 {
    let mut num = 0.0;
    let mut base = None;
    for ch in s.chars() {
        parse_float(&mut num, &mut base, ch);
    }
    num
}

pub fn main() {
    println!("{}", parse("42"));
    println!("{}", parse("4.2"));
    println!("{}", parse(".42"));
}
// fn add_to_char_or_str_or_dispatch_and_rewind(
//     c: char,
//     t: Token,
//     ts: &mut Vec<Token>,
//     counter: &mut u32,
// ) -> Result<Option<Token>, LexErr> {
//     use LexErrType::CharsGtOne;
//     use LitType::{Char, Str};
//     use TokenType::{Lit, Start};

//     let line = t.line;
//     let character = t.character;

//     match push_non_spec_to_char_str_or_comment(t, c) {
//         Ok(new_t) => Ok(Some(new_t?)),
//         Err(t) => match t.token_type {
//             _ => {
//                 t.dispatch(ts);
//                 *counter -= 1;
//                 Ok(None)
//             }
//         },
//     }
//     match t.token_type {
//         Start(StartType::Char) => Ok(Some(t.update(Lit(Char(c))))),
//         Start(StartType::Str) => Ok(Some(t.update(Lit(Str(String::from(c)))))),
//         Lit(Char(_)) => Err(t.err(CharsGtOne)),
//         Lit(Str(s)) => Ok(Some(Token::new(
//             line,
//             character,
//             Lit(Str(s.clone() + &String::from(c))),
//         ))),
//         _ => {
//             t.dispatch(ts);
//             *counter -= 1;
//             Ok(None)
//         }
//     }
// }

//fn close_or_start_new(
//    tokens: &mut Vec<Token>,
//    c: char,
//    token: Token,
//    line: u16,
//    character: u16,
//    new_token: TokenType,
//) -> Result<Option<Token>, LexErr> {
//    Ok(match token.token_type {
//        TokenType::Lit(LitType::Char(mc)) => token.update(close_char(mc, c, token)?),
//        TokenType::Lit(LitType::Str(ms)) => token.update(TokenType::Lit(LitType::Str(Some(
//            ms.map(|s| s + &String::from(c)).unwrap_or(String::from(c)),
//        )))),
//        _ => token_dispatch!(tokens, token, Token::new(line, character, new_token)),
//    })
//}

// fn close_char(s: StartType, c: char, token: Token) -> Result<TokenType, LexErr> {
//     match mc {
//         Some(_) => Err(LexErr {
//             line: token.line,
//             character: token.character,
//             err_type: LexErrType::CharsGtOne,
//         }),
//         None => Ok(TokenType::Lit(LitType::Char(Some(c)))),
//     }
// }
*/
