module MutuallyRecursive

let rec foo (l: list int) : Tot int (decreases %[l; 0]) =
  match l with
  | [] -> 0
  | _ :: xs -> bar xs

and bar (l: list int) : Tot int (decreases %[l; 1]) =
  foo l

let rec foo2 (l: list int) : int =
  match l with
  | [] -> 0
  | _ :: xs -> foo2 xs

type tree =
  | Terminal : tree
  | Internal : node -> tree

and node =
  {
    left: tree;
    data: int;
    right: tree
  }

let rec incr_tree (t: tree) : tree =
  match t with
  | Terminal -> Terminal
  | Internal node -> 
    assert (node.left << t);
    assert (node.right << t);
    Internal (incr_node node)

and incr_node (n: node) : node =
  {
    left = incr_tree n.left;
    data = n.data + 1;
    right = incr_tree n.right
  }

let tree1 : tree = Terminal
let tree2 : tree = Internal { left = tree1; data = 1; right = tree1; }
let chat_is_this_real =
  match tree2 with
  | Terminal -> ()
  | Internal n -> assert (n.left << n)