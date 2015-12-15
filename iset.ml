(*Zadanie: iSet*)
(*Autor: Paweł Zięcik*)
(*Recenzent: Artur Jamro*)

(*Reprezentacja: Node(l, (x, y), r, h, n)
  [x, y] - przedzial (x <= y), h - wysokosc
  n - minimum z liczby elementow w drzewie i max_int
  l, r - odpowiedznio lewe, prawe drzewo*)

type interval = int * int

type t = Empty | Node of t * interval * t * int * int  

let empty = Empty

let satSum a = (*zmienia liczbe na max_int jesli *) 
  if a >= 0 then a else max_int  (*przekroczono zakres*)

let is_empty l = l = Empty 

let height = function
  | Empty -> 0
  | Node (_, _, _, h, _) -> h

let size = function
  | Empty -> 0
  | Node(_, _, _, _, n) -> n

let make l ((x, y) as p) r =
  Node(l, p, r, max (height l) (height r) + 1, 
  satSum (size l + size r + y - x + 1))

let bal l ((x, y) as p) r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lp, lr, _, _) ->
      if height ll >= height lr 
        then make ll lp (make lr p r)
        else
          (match lr with
          | Node (lrl, lrp, lrr, _, _) ->
            make (make ll lp lrl) lrp (make lrr p r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rp, rr, _, _) ->
      if height rr >= height rl 
        then make (make l p rl) rp rr
        else
          (match rl with
          | Node (rll, rlp, rlr, _, _) ->
            make (make l p rll) rlp (make rlr rp rr) 
          | Empty -> assert false)
    | Empty -> assert false
  else Node(l, p, r, max hl hr + 1,
    satSum (size l + size r + y - x + 1))

let rec addOneRight a t = (*Znajduje przedział ktorego koniec  = a*) 
  match t with            (*i usuwa go z drzewa*)
  | Empty -> (Empty, (a + 1))   (*Przedzialu nie znaleziono*)
  | Node(l, (x, y), r, _, _) -> (*Zakladamy y <= a dla kazdego*)
    if y = a                  (*przedzialu w poddrzewach*) 
      then (l, x)
      else
        let rt, lend = addOneRight a r in
          (bal l (x, y) rt, lend)

let rec addOneLeft b t = (*Znajduje przedzial ktorego poczatek = b*)
  match t with           (*i usuwa go z drzewa*)
  | Empty -> (Empty, (b - 1))  (*Przedzialu nie znaleziono*)
  | Node(l, (x, y), r, _, _) -> (*Zakladamy b <= x dla kazdego*)
    if x = b                  (*przedzialu w poddrzewach*)
      then (r, y)
      else
        let lt, rend = addOneLeft b r in
          (bal l (x, y) lt, rend)

let rec addOne ((a, b) as p) t = (*Zakladamy ze zostalo wykonane remove x y*) 
  match t with
  | Empty -> make Empty p Empty
  | Node(l, (x, y), r, _, _) ->
    if b + 1 < x 
      then bal (addOne p l) (x, y) r
      else if y + 1 < a
        then bal l (x, y) (addOne p r)
        else if y + 1 = a 
          then
            let rt, rend = addOneLeft (b + 1) r in
              bal l (x, rend) rt
          else
            let lt, lend = addOneRight (a - 1) l in
              bal lt (lend, y) r 

let rec join l p r = 
  match (l, r) with
  | (Empty, _) -> addOne p r
  | (_, Empty) -> addOne p l
  | (Node(ll, lp, lr, lh, _), Node(rl, rp, rr, rh, _)) ->
    if lh > rh + 2 
      then bal ll lp (join lr p r) 
      else
        if rh > lh + 2 
          then bal (join l p rl) rp rr 
          else make l p r

let split v t =
  let rec loop = function
    | Empty ->
      (Empty, false, Empty)
    | Node (l, (x, y), r, _, _) ->
      if v < x 
        then
          let (ll, pres, rl) = loop l in 
            (ll, pres, join rl (x, y) r) 
        else if y < v 
          then
            let (lr, pres, rr) = loop r in 
              (join l (x, y) lr, pres, rr) 
          else  
            let l = if x < v then addOne (x, v - 1) l else l in
            let r = if y > v then addOne (v + 1, y) r else r in 
              (l, true, r)      
  in loop t

let rec minElt = function
  | Node(Empty, p, _, _, _) -> p
  | Node(l, _, _, _ , _) -> minElt l
  | Empty -> raise Not_found

let rec removeMinElt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, p, r, _, _) -> bal (removeMinElt l) p r
  | Empty -> invalid_arg "ISet.remove_min_elt"

let merge t1 t2 = 
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
    let p = minElt t2 in
    bal t1 p (removeMinElt t2)

let remove (x, y) t =
  let (l, _, _) = split x t in
  let (_, _, r) = split y t in
    merge l r

let add p t =
  let t = remove p t in
    addOne p t

let rec mem v = function
  | Empty -> false
  | Node(l, (x, y), r, _, _) ->
    if x <= v && v <= y 
      then true
      else if v < x 
        then mem v l
        else mem v r

let rec iter f = function
  | Empty -> ()
  | Node (l, (x, y), r, _, _) ->
    iter f l; f (x, y); iter f r

let rec fold f t a =
  match t with
  | Empty -> a
  | Node(l, (x, y), r, _, _) ->
    fold f r (f (x, y) (fold f l a))

let elements t =
  let rec loop t a =   
    match t with
    | Empty -> a
    | Node(l, (x, y), r, _, _) -> loop l ((x, y)::(loop r a))
  in loop t []

let below v t =
  let rec loop t acc = 
    match t with
    | Empty -> acc
    | Node(l, (x, y), r, _, n) ->
      if v > y
        then loop r (satSum (acc + size l + y - x + 1))
        else if x <= v
          then loop l (satSum (acc + v - x + 1)) 
          else loop l acc  
  in 
    let n = loop t 0 in
    if n < 0 || (v = max_int && not (is_empty t)) 
      then max_int
      else n

