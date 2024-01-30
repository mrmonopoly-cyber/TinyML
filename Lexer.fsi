module TinyML.Lexer

/// Rule comment
val comment: level: obj -> lexbuf: LexBuffer<char> -> token
/// Rule linecomment
val linecomment: lexbuf: LexBuffer<char> -> token
/// Rule tokenize
val tokenize: lexbuf: LexBuffer<char> -> token
