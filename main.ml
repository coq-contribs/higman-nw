open Higman

exception Invalid

let rec random_word = function
    0 -> Emptyword 
  | n -> let w = random_word (n-1) in
    if (Random.int 2) = 1 then Cons (A1,w)
    else Cons (A0,w)

let rec string_of_word = function 
    Emptyword -> ""
  | Cons(A0,w)-> "0"^(string_of_word w)
  | Cons(A1,w)-> "1"^(string_of_word w)
      
let word_of_string s = 
  let n = String.length s in 
  let rec aux i = 
    if i=n then Emptyword
    else match s.[i] with  
      | '0' -> Cons (A0,aux (i+1))
      | '1' -> Cons (A1,aux (i+1))
      | _ -> raise Invalid
  in aux 0 

let rec random_function () = 
  let h = Hashtbl.create 153 in 
  fun n -> 
    try
      Hashtbl.find h n
    with Not_found -> 
      let w = random_word (1+(Random.int 19)) in 
      Hashtbl.add h n w; w

let rec i2n = function 0 -> O | n -> S (i2n (n-1)) 
 
let rec n2i = function O -> 0 | S n -> succ (n2i n)

let _ = 
  Random.self_init();
  try 
    let nargs = Array.length Sys.argv - 1 in 
    if nargs = 0 then raise Invalid;
    if Sys.argv.(1) = "--help" || Sys.argv.(1) = "-h" then 
      begin
	print_string "\nhigman\n";
	print_string "------\n";
	print_string "Program extracted from Higman proof\n";
	print_string "Proof by Hugo Herbelin, Extraction by Pierre Letouzey\n\n";
	print_string "usage:\n\n";
	print_string "--help\t\t this little help\n";
	print_string "--random\t run on a random word sequence\n";
	print_string "n0 n1 ...\t run on the given sequence (filled with empty words)\n\n";
	exit 0
      end;
    let f = 
      if Sys.argv.(1) = "--random" then random_function ()
      else 
	let words = 
	  Array.create nargs Emptyword in 
	for i = 1 to nargs do 
	  words.(i-1) <- word_of_string Sys.argv.(i)
	done; 
	function n -> 
	  let i = n2i n in 
	  if i>=nargs then Emptyword 
	  else words.(i)
    in 
    let A_intro (i,j) = higman f in 
    let i = n2i i and j = n2i j in 
    for k = 0 to j do 
      Printf.printf "f(%d)=%s\n" k (string_of_word (f (i2n k)))
    done;
    Printf.printf "f(%d)=...\n" (j+1);
    Printf.printf "==> f(%d) is included in f(%d)\n" i j ;
    exit 0;
  with Invalid -> print_string "Invalid argument\n" ; exit 1
