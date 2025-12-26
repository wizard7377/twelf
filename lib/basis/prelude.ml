

type order = Less | Equal | Greater

let less : order = Less
let equal : order = Equal
let greater : order = Greater
let print s = print_string s ;;
let rev lst = Stdlib.List.rev lst ;;
