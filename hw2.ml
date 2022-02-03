(* 
   Homework Assignment 2
   Nidhi Parekh
   Pledge: I pledge my honor that I have abided by the Stevens Honor System.
   Date: 13 June 2021

*)


(**node - pair of some 'a value & a list of 'a general tree *)
type 'a gt = Node of 'a * ('a gt) list

let t : int gt =
   Node (33,
      [Node  (12 ,[]);
      Node (77,
         [Node (37,
            [Node (14, [])]);
               Node (48, []);
               Node  (103,  [])])])


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let rec height: 'a gt -> int = 
   fun (Node(_, nodes)) ->
      1 + (List.fold_left max 0 (List.map height nodes))



(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let add =
   fun x y ->
   x + y

let rec size : 'a gt -> int =
  fun t ->
  match t with
  | Node(_,[]) -> 1
  | Node(_,nodes) -> 1 + (List.fold_left add 0 (List.map size nodes))


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)
 

let rec paths_to_leaves =
   fun t ->
   match t with 
   | Node(_,[]) -> [[]]
   | Node(_,nodes) -> 
   let rec path_to_leaves_helper =
      fun nodes_list path_value ->
      match nodes_list with
      | [] -> []
      | h::t -> (List.map (fun i -> path_value::i) (paths_to_leaves h)) @ path_to_leaves_helper t (path_value + 1)
   in path_to_leaves_helper nodes 0 


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)


let rec is_leaf_perfect_helper = 
   fun l ->
   match l with
   | [] -> true 
   | [x] -> true
   | h::n::t -> h ==n && (is_leaf_perfect_helper (n::t))

   
let rec is_leaf_perfect : 'a gt -> bool = 
    fun (Node(d,ch)) ->
    match ch with
    | [] -> true
    | h::t -> List.fold_left (fun x y -> x && y) true (List.map is_leaf_perfect ch)
    && is_leaf_perfect_helper (List.map height ch) 
               

  

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)


let rec preorder =
   fun (Node(d,ch)) ->
   [d] @ List.fold_left (fun accumulate x -> accumulate @ x) [] (List.map preorder ch)



(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let rec mirror =
   fun (Node(d,ch)) ->
   Node(d,List.rev(List.map mirror ch))


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

(**similar to ex.ml example of mapt*)
let rec mapt : ('a -> 'b) -> 'a gt -> 'b gt =
   fun f (Node(d,ch)) ->
   Node(f d, List.map (mapt f) ch)

(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

(**similar to ex.ml example of foldt*)
let rec foldt : ('a -> 'b list -> 'b) -> 'a gt -> 'b =
   fun f (Node(d,ch)) ->
   f d (List.map (foldt f) ch)


(*--------------------------------------------------------------------------------------------------------------------------------------------------------*)

let sumt t = 
   foldt (fun i rs -> i + List.fold_left (fun i j -> i+j) 0 rs) t

let  memt t e =
   foldt (fun i rs -> i=e || List.exists (fun i -> i) rs) t


let mirror' =
   fun (Node(d,ch)) ->
   foldt (fun i rs -> Node(i, List.rev rs)) (Node(d,ch))


