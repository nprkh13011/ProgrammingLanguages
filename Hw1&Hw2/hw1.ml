(* 
   Homework Assignment 1
   Nidhi Parekh
   Pledge: I pledge my honor that I have abided by the Stevens Honor System.
   Date: 6 June 2021
*)

(*
      Encoding      Instruction
        0             Pen down
        1              Pen up
        2            Move North
        3             Move East 
        4            Move South 
        5            Move West
*)

type program = int list
let square : program = [0; 2; 2; 3; 3; 4; 4; 5; 5; 1]
let letter_e : program = [0;2;2;3;3;5;5;4;3;5;4;3;3;5;5;1]

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*) 
let rec mirror_image_helper =
  fun n ->
  match n with
  | 0 -> 0                      (* if 0 = 0 *)
  | 1 -> 1                      (* if 1 = 1 *)
  | m -> if m==2 || m==3        (* if 2 or 3 = add by 2, if 4 or 5 = sub by 2*)
         then m+2 
         else m - 2

let mirror_image : int list -> int list = 
  fun l ->
  List.map mirror_image_helper l

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let rec rotate_90_letter_helper =
  fun n ->
  match n with        
  | 0 -> 0                                (* if 0 or 1, return 0,1 respectively *)
  | 1 -> 1                
  | n -> if n == 2 || n == 3 || n == 4    (* if 2, 3, 4 in the list, then add by 1. Otherwise sub by 3 *)
         then n + 1
         else n - 3


let rotate_90_letter : int list -> int list =
 fun l ->
 List.map rotate_90_letter_helper l

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let rotate_90_word : int list list -> int list list=
 fun l ->                       
 List.map rotate_90_letter l               (* similar as rotate_90_letter *)

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let rec repeat : int ->'a -> 'a list =
  fun n x ->
  match n with
  | 0 -> []
  | m when m>0 -> x::repeat (m-1) x
  | _ -> [] (*n is negative*)

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)


(**Helper functions *)
let rec pantograph_helper = (** similar to the repeat function *)
  fun n p ->
  match p with
  | 0 -> [p]
  | 1 -> [p]
  | _ -> 
        if n==0 
        then []
        else p::pantograph_helper (n-1) p

let rec delete d = (* makes everything into 1 long list -- deletes extra [] *)
  match d with 
  | [] -> []
  | h::t -> h @ delete t


let rec pantograph_f_helper = (**return a list that is concatenated with [] in fold_left *)
  fun n p ->
  match n with
  | 0 -> []
  | _ -> 
    if (p == 0 || p == 1) 
    then [p]
    else repeat n p 

 (**returns a program that draws the same things as p only enlarged n-fold. *)
 let rec pantograph_nm : int -> int list -> int list = 
  fun n p ->
  match p with
  | [] -> []
  | h::t -> 
    if (h == 0 || h == 1) (** if 0, 1 then it will either be the starting point or ending point of the list *)
    then h::pantograph_nm n t
    else repeat n h @ pantograph_nm n t  (* otherwise, use the repeat function and returns p with however many copies of n  *)

(*Includes map*)
let pantograph : int -> int list -> int list = 
  fun n p ->
  delete(List.map (pantograph_helper n) p)


(**same function but using fold_left*)
let pantograph_f = 
  fun n p ->   
  List.fold_left (fun accumulate x -> accumulate @ pantograph_f_helper n x) [] p


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

(**Coverage checks to see if the list is empty, if not, calls coverage _helper
 and adds it to the list and recurses with the tail and the updated version of the coordinates *)
let coverage_helper =
  fun tup op ->
  match tup with 
  |x,y ->
    match op with 
    |2 -> (x,y+1)
    |3 -> (x+1,y)
    |4 -> (x,y-1)
    |5 -> (x-1,y)
    |i -> tup

let rec coverage: int*int -> int list -> (int*int) list =
  fun n l ->
  match l with
  |[] -> []
  |h::t -> [coverage_helper n h] @ coverage(coverage_helper n h) t


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)


let rec compress_helper = 
  fun l n count->
  match l with 
  | [] -> [(n, count)]
  | h::t ->
          if n = h            (** if the num in list (as it continues to go through the list) = head of the list, it will add to count until it reaches the final consecutive number *)
          then compress_helper t n (count + 1)
          else (n, count) :: compress_helper t h 1 (** otherwise, if there is no consecutive number (same num) after the prev one, the count will be 1*)


let compress : int list -> (int*int) list =
  fun l ->
  match l with
  | []->[]                                  (** checks if the list is empty, if not, it goes thru the list and starts the count at 0 & goes thru the helper function *)
  | h::t -> compress_helper l h 0 


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)


let rec uncompress_helper =
  fun (a, b) -> (**number of times u wnt to repeat and number that needs to be repeated *)
    repeat b a


let rec uncompress : (int*int) list -> int list =
  fun l ->
  match l with
  | [] -> []
  | h::t -> uncompress_helper h @ uncompress t (**two lists together *)
  

let uncompress_m : (int*int) list -> int list =
  fun l ->
  delete(List.map (uncompress_helper) l)  (**deletes  any extra [] that may come*)


let uncompress_f : (int*int) list -> int list =
  fun l ->
  List.fold_left(fun f x -> f @ (uncompress_helper x)) [] l


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)


(* helper receives 1s and 0s as the p parameter, and the helper basically removes duplicates of whatever number it’s being inputted *)
  let rec optimize_helper =
    fun l p -> (* p carries the current state of the pen *)
    match l with
    | [] -> []
    | h::t -> if (h==p) 
                then (optimize_helper t p)
                else if (h==0) 
                    then h::(optimize_helper t 0)
                    else if (h==1) 
                         then h::(optimize_helper t 1)
                          else h::(optimize_helper t p)

let rec optimize : program -> program =
    fun l ->
    optimize_helper l 1