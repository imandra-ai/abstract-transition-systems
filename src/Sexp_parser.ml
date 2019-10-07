module Fmt = CCFormat
type sexp = CCSexp.t
type error =
  | E_one_of of (string * error) list
  | E_fail of string
  | E_parsing of string * error

type 'a t = sexp -> ('a, error) result

let rec pp_error out e =
  match e with
  | E_fail msg -> Fmt.fprintf out "%a" Fmt.text msg
  | E_parsing (what, e) ->
    Fmt.fprintf out "@[while parsing %S:@ %a@]" what pp_error e
  | E_one_of l ->
    let pp_one out (what,e) =
      Fmt.fprintf out "@[%S:@ %a@]" what pp_error e
    in
    Fmt.fprintf out "@[<hv>none of the choices worked:@ %a@]"
      Fmt.(list ~sep:(return ";@ ") pp_one) l

let string_of_error e = Fmt.asprintf "%a@?" pp_error e

let return x _sexp = Ok x
let fail msg _sexp = Error (E_fail msg)
let failf fmt = Fmt.ksprintf ~f:fail fmt

let err_ msg sexp = Error (E_fail (Fmt.asprintf "%s@ but got %a" msg CCSexp.pp sexp))

let int : int t = function
  | `Atom x as s -> (try Ok (int_of_string x) with _ -> err_ "expected int" s)
  | s -> err_ "expected int" s

let bool : bool t = function
  | `Atom x as s -> (try Ok (bool_of_string x) with _ -> err_ "expected bool" s)
  | s -> err_ "expected bool" s

let float : float t = function
  | `Atom x as s -> (try Ok (float_of_string x) with _ -> err_ "expected float" s)
  | s -> err_ "expected float" s

let string : string t = function
  | `Atom x -> Ok x
  | s -> err_ "expected atom" s

let value : sexp t = fun x -> Ok x

let list_value : sexp list t = function
  | `List x -> Ok x
  | `Atom _ as s -> err_ "expected list" s

let list (f: 'a t) : 'a list t = function
  | `List l ->
    let rec map_ acc = function
      | [] -> Ok (List.rev acc)
      | x :: tl ->
        match f x with
        | Ok x' -> map_ (x'::acc) tl
        | Error e -> Error e
    in
    map_ [] l
  | `Atom _ as s -> err_ "expected list" s

let list1 f = function
  | `List [x] -> f x
  | s -> err_ "expected unary list" s

let list2 f1 f2 = function
  | `List [x1; x2] ->
    CCResult.(pure (fun x y -> x,y) <*> f1 x1 <*> f2 x2)
  | s -> err_ "expected binary list" s

let list3 f1 f2 f3 = function
  | `List [x1; x2; x3] ->
    CCResult.(pure (fun x y z -> x,y,z) <*> f1 x1 <*> f2 x2 <*> f3 x3)
  | s -> err_ "expected ternary list" s

let list4 f1 f2 f3 f4 = function
  | `List [x1; x2; x3; x4] ->
    CCResult.(pure (fun x y z w -> x,y,z,w) <*> f1 x1 <*> f2 x2 <*> f3 x3 <*> f4 x4)
  | s -> err_ "expected 4 elts list" s

let is_nil = function `List [] -> Ok true | _ -> Ok false

let rec fix f sexp = f (fix f) sexp

let one_of l sexp =
  let rec loop errs = function
    | [] -> Error (E_one_of errs)
    | (name1,p1) :: ps ->
      match p1 sexp with
      | Ok x -> Ok x
      | Error e -> loop ((name1,e)::errs) ps
  in
  loop [] l

let uncons (p:'a t) (f:'a -> 'b t) : 'b t =
  function
  | `Atom _ as s -> err_ "uncons: expected list" s
  | `List [] as s -> err_ "uncons: expected non-empty list" s
  | `List (x :: l) ->
    match p x with
    | Ok x -> f x (`List l)
    | Error e -> Error e

let match_ ~atom ~list sexp = match sexp with
  | `Atom _ -> atom sexp
  | `List _ -> list sexp

let (>|=) p f sexp = match p sexp with
  | Ok x -> Ok (f x)
  | Error e -> Error e

let (>>=) p f sexp = match p sexp with
  | Ok x -> f x sexp
  | Error e -> Error e

let parsing what p sexp = match p sexp with
  | Ok x -> Ok x
  | Error e -> Error (E_parsing (what, e))

module Infix = struct
  let (>>=) = (>>=)
  let (>|=) = (>|=)
end

let parse_string p s =
  match CCSexp.parse_string s with
  | Error s -> Error (E_fail s)
  | Ok x -> p x

let parse_string_str p s =
  CCResult.map_err string_of_error (parse_string p s)

let parse_file p s =
  match CCSexp.parse_file s with
  | Error s -> Error (E_fail s)
  | Ok x -> p x

let parse_file_str p s =
  CCResult.map_err string_of_error (parse_file p s)
