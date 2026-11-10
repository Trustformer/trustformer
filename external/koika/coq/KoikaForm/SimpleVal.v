Require Import Koika.KoikaForm.Types.

Inductive val :=
| Bits (v: list bool)
| Enum (sig: enum_sig) (v: list bool)
| Struct (sig: struct_sig) (v: list val)
| Array (sig: array_sig) (v: list val).

Fixpoint val_of_value {tau: type} (x: type_denote tau) {struct tau} : val :=
  let val_of_struct_value := (
    fix val_of_struct_value {fields} (x: struct_denote fields) : list val :=
      match fields return struct_denote fields -> list val with
      | [] => fun _ => []
      | (nm, tau) :: fields => fun '(x, xs) =>
        val_of_value x :: (val_of_struct_value xs)
      end x
  ) in
  match tau return type_denote tau -> val with
  | bits_t   sz  => fun bs  => Bits       (vect_to_list bs)
  | enum_t   sig => fun bs  => Enum   sig (vect_to_list bs)
  | struct_t sig => fun str => Struct sig (val_of_struct_value str)
  | array_t  sig => fun v   => Array  sig (map val_of_value (vect_to_list v))
  end x.

Fixpoint ubits_of_value (v: val) : list bool :=
  match v with
  | Bits     bs => bs
  | Enum   _ bs => bs
  | Struct _ lv => List.concat (rev (map ubits_of_value lv))
  | Array  _ lv => List.concat (rev (map ubits_of_value lv))
  end.
