exception Parse_error of string

let assoc_opt n e =
  try Some (List.assoc n e) with
    Not_found -> None

type value =
    Literal of string
  | Unary of string * value
  | Binary of string * value * value
  | Tertiary of string * value * value * value

type operator =
  {
    name : string ;
    lbp : int ;
    rbp : int ;
    led : value -> value ;
    nud : unit -> value ;
  }

let is_op t env =
  match assoc_opt t env with
  | Some _ -> true
  | None -> false

let lbp token env =
  match assoc_opt token env with
  | None -> 0
  | Some {lbp = i} -> i

let nud token env =
    match assoc_opt token env with
    | Some {nud = f} -> f
    | None -> (fun () -> Literal token)

let led token env =
    match assoc_opt token env with
    | Some {led = f} -> f
    | None -> raise (Parse_error (token ^ " is not an infix operator"))

let emptyEnv = []

let source_string_stream str =
  let source = Scanf.Scanning.from_string str in
  Stream.from (fun i ->
    try Scanf.bscanf source "%c" (fun x -> Some x) with
    End_of_file -> None
  )

let lexer input =
  let between ch a b = a <= ch && ch <= b in
  let is_digit ch = between ch '0' '9' in
  let is_letter ch = (between ch 'a' 'z') || (between ch 'A' 'Z') in
  let is_whitespace ch = ch = ' ' || ch = '\t' || ch = '\n' in
  let is_symbol ch =
    begin
      let symbols = "~!@#$%^&*()_-+=[]{}:;'<>?,./|" in
      try ignore (String.index symbols ch); true with
      | Not_found -> false
    end
  in
  let read_object classifier =
    (fun stream ->
      let rec obj s b =
        let ch = Stream.peek s
        in
        match ch with
        | Some c ->
          if classifier c
          then (Buffer.add_char b (Stream.next s); obj s b)
          else Buffer.contents b
        | None -> Buffer.contents b
      in obj stream (Buffer.create 16)
    )
  in
  let read_number = read_object is_digit in
  let read_word = read_object is_letter in
  let read_symbol = read_object is_symbol in
  let read_whitespace = read_object is_whitespace in
  Stream.from (fun (i) ->
      ignore (read_whitespace input);
      match Stream.peek input with
      | None -> None
      | Some c ->
        if is_digit c
        then Some (read_number input)
        else if is_letter c
        then Some (read_word input)
        else if is_symbol c
        then Some (read_symbol input)
        else None)

let infix op_name power parse tokens =
    {
      name = op_name ;
      lbp = power ;
      rbp = power ;
      led = (fun left -> Binary (op_name, left, (parse power (Stream.next tokens)))) ;
      nud = (fun () -> raise (Parse_error (op_name ^ "is not a prefix operator"))) ;
    }

let pre_or_infix op_name lpow rpow parse tokens =
    {
      name = op_name ;
      lbp = lpow ;
      rbp = rpow ;
      led = (fun left -> Binary (op_name, left, (parse rpow (Stream.next tokens)))) ;
      nud = (fun () -> Unary (op_name, (parse lpow (Stream.next tokens)))) ;
    }

let delim op_name =
    {
      name = op_name ;
      lbp = 0 ;
      rbp = 0 ;
      led = (fun left -> raise (Parse_error (op_name ^ " is not an infix operator"))) ;
      nud = (fun () -> raise (Parse_error (op_name ^ " is not a prefix operator"))) ;
    }

let infixr op_name power parse tokens =
    {
      name = op_name ;
      lbp = power ;
      rbp = power - 1 ;
      led = (fun left -> Binary (op_name, left, (parse (power - 1) (Stream.next tokens)))) ;
      nud = (fun () -> raise (Parse_error (op_name ^ " is not a prefix operator"))) ;
    }

let prefix op_name power close parse tokens expect =
    {
      name = op_name ;
      lbp = power ;
      rbp = 0 ;
      led = (fun left -> raise (Parse_error (op_name ^ " is not an infix operator"))) ;
      nud = (fun () ->
          let right = parse 0 (Stream.next tokens)
          in expect close ; right )
    }

let preinfix op_name power sep parse tokens expect =
    {
      name = op_name ;
      lbp = power ;
      rbp = 0 ;
      led = (fun left -> raise (Parse_error (op_name ^ " is not an infix operator"))) ;
      nud = (fun () ->
          let arg = parse 0 (Stream.next tokens) in
          expect sep ;
          let body = parse 0 (Stream.next tokens) in
          Binary (op_name, arg, body)
        )
    }

let tertiary op_name power sep1 sep2 parse tokens expect =
  {
      name = op_name ;
      lbp = power ;
      rbp = 0 ;
      led = (fun left -> raise (Parse_error (op_name ^ " is not an infix operator"))) ;
      nud = (fun () ->
          let first = parse 0 (Stream.next tokens) in
          expect sep1 ;
          let second = parse 0 (Stream.next tokens) in
          expect sep2 ;
          let third = parse 0 (Stream.next tokens) in
          Tertiary ((op_name ^ "/" ^ sep1 ^ "/" ^ sep2), first, second, third)
        )    
  }

let pratt_parse tokens =
  let the_ops = ref emptyEnv in
  let expect n =
    match Stream.peek tokens with
    | None -> raise (Parse_error ("expected " ^ n ^ " but found nothing"))
    | Some t ->
      if n = t
      then ignore (Stream.next tokens)
      else raise (Parse_error ("expected " ^ n ^ " but found " ^ t))
  in
  let rec parse rbp token =
    let rec leds left =
      match Stream.peek tokens with
      | None -> left
      | Some t ->
        if is_op t !the_ops
        then
          begin
            if rbp < (lbp t !the_ops)
            then
              leds ((led (Stream.next tokens) !the_ops) left)
            else
              left
          end
        else
          begin
            if rbp < (lbp "@" !the_ops)
            then
              leds ((led "@" !the_ops) left)
            else
              left
          end
    in leds ((nud token !the_ops)())
  in
  let ops = List.fold_left
      (fun a ({name = n} as x) -> (n, x)::a)
      emptyEnv
      [
        tertiary "if" 5 "then" "else" parse tokens expect ;
        delim "then" ;
        delim "else" ;

        infix "=" 10 parse tokens ;

        pre_or_infix "+" 30 20 parse tokens ;
        pre_or_infix "-" 30 20 parse tokens ;

        infix "*" 30 parse tokens ;

        infixr "**" 40 parse tokens ;

        infix "@" 50 parse tokens ;

        preinfix "fn" 55 "->" parse tokens expect ;
        delim "->" ;

        preinfix "let" 55 "in" parse tokens expect ;
        delim "in" ;

        prefix "(" 60 ")" parse tokens expect ;
        delim ")" ;

      ]
  in
  the_ops := ops ; parse 0 (Stream.next tokens)

let tests () =
  let cases = [
    "a + 2" ;
    "5 - 3" ;
    "-3 * 7" ;
    "2 * 3 + 4" ;
    "2 * (3 + 4)" ;
    "2 ** 3 ** 4" ;
    "-3**2" ;
    "fn a -> a + 3" ;
    "function arg args 3" ;
    "(fn a -> a + 3) 7" ;
    "let x = 2 in x * 3" ;
    "let id = fn x -> x in id 3 " ;
    "let x = 2 in let y = 3 in y - x" ;
    "if 7 then 8 else 9" ;
    "if 7 then let x = 8 in x else 9 -5" ;
  ] in
  List.map (fun c -> pratt_parse (lexer (source_string_stream c))) cases
