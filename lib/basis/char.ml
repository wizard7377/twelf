open Order
module type CHAR = sig
    type char = Stdlib.Char.t
    type string = Stdlib.String.t

    val minChar : char
    val maxChar : char
    val maxOrd : int

    val ord : char -> int
    val chr : int -> char
    val succ : char -> char
    val pred : char -> char

    val compare : char * char -> order
    val ( < )  : char * char -> bool
    val ( <= ) : char * char -> bool
    val ( > ) : char * char -> bool
    val ( >= ) : char * char -> bool

    val contains : string -> char -> bool
    val notContains : string -> char -> bool

    val isAscii : char -> bool
    val toLower : char -> char
    val toUpper : char -> char
    val isAlpha : char -> bool
    val isAlphaNum : char -> bool
    val isCntrl : char -> bool
    val isDigit : char -> bool
    val isGraph : char -> bool
    val isHexDigit : char -> bool
    val isLower : char -> bool
    val isPrint : char -> bool
    val isSpace : char -> bool
    val isPunct : char -> bool
    val isUpper : char -> bool

    val toString : char -> string
end

module Char : CHAR = struct
    
    type char = Stdlib.Char.t
    type string = Stdlib.String.t

    let minChar : char = assert false
    let maxChar : char = assert false
    let maxOrd : int = assert false

    let ord : char -> int = assert false
    let chr : int -> char = assert false
    let succ : char -> char = assert false
    let pred : char -> char = assert false

    let compare : char * char -> order = assert false
    let ( < )  : char * char -> bool = assert false
    let ( <= ) : char * char -> bool = assert false
    let ( > ) : char * char -> bool = assert false
    let ( >= ) : char * char -> bool = assert false

    let contains : string -> char -> bool = assert false
    let notContains : string -> char -> bool = assert false

    let isAscii : char -> bool = assert false
    let toLower : char -> char = assert false
    let toUpper : char -> char = assert false
    let isAlpha : char -> bool = assert false
    let isAlphaNum : char -> bool = assert false
    let isCntrl : char -> bool = assert false
    let isDigit : char -> bool = assert false
    let isGraph : char -> bool = assert false
    let isHexDigit : char -> bool = assert false
    let isLower : char -> bool = assert false
    let isPrint : char -> bool = assert false
    let isSpace : char -> bool = assert false
    let isPunct : char -> bool = assert false
    let isUpper : char -> bool = assert false

    let toString : char -> string = assert false
end
