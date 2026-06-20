import BijForm.DependentPolynomial

namespace BijForm
namespace StringDiagram

open DepPoly

/-- Remove the element at a proof-carrying index. -/
def eraseFin {α : Type} : (xs : List α) → Fin xs.length → List α
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => xs
  | x :: xs, ⟨n + 1, h⟩ =>
      x :: eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩

theorem eraseFin_eq_eraseIdx {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      eraseFin xs i = xs.eraseIdx i.val
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => by
      simp [eraseFin]
  | x :: xs, ⟨n + 1, h⟩ => by
      have ih := eraseFin_eq_eraseIdx xs
        ⟨n, Nat.lt_of_succ_lt_succ h⟩
      simp [eraseFin, ih]

@[simp]
theorem eraseFin_length {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      (eraseFin xs i).length = xs.length - 1
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => by simp [eraseFin]
  | x :: xs, ⟨n + 1, h⟩ => by
      have ih := eraseFin_length xs ⟨n, Nat.lt_of_succ_lt_succ h⟩
      have htail : n < xs.length := Nat.lt_of_succ_lt_succ h
      have hpos : 0 < xs.length := Nat.lt_of_le_of_lt (Nat.zero_le n) htail
      simp [eraseFin, ih]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)

theorem eraseFin_pointwise_relation {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length)
    (hrel :
      ∀ (n : Nat) (hx : n < xs.length) (hy : n < ys.length),
        R (xs.get ⟨n, hx⟩) (ys.get ⟨n, hy⟩))
    (ix : Fin xs.length) (iy : Fin ys.length)
    (hindex : ix.val = iy.val)
    (n : Nat)
    (hx : n < (eraseFin xs ix).length)
    (hy : n < (eraseFin ys iy).length) :
    R ((eraseFin xs ix).get ⟨n, hx⟩)
      ((eraseFin ys iy).get ⟨n, hy⟩) := by
  revert ys ix iy n
  induction xs with
  | nil =>
      intro ys hlen hrel ix iy hindex n hx hy
      cases ix with
      | mk val isLt =>
          exact False.elim (Nat.not_lt_zero val isLt)
  | cons x xs ih =>
      intro ys hlen hrel ix iy hindex n hx hy
      cases ys with
      | nil =>
          simp at hlen
      | cons y ys =>
          have htailLen : xs.length = ys.length := Nat.succ.inj hlen
          cases ix with
          | mk ixVal ixLt =>
              cases iy with
              | mk iyVal iyLt =>
                  cases ixVal with
                  | zero =>
                      cases iyVal with
                      | zero =>
                          simp
                          apply hrel (n + 1)
                          · simpa using Nat.succ_lt_succ hx
                          · simpa using Nat.succ_lt_succ hy
                      | succ iyVal =>
                          have hbad := hindex
                          simp at hbad
                  | succ ixVal =>
                      cases iyVal with
                      | zero =>
                          have hbad := hindex
                          simp at hbad
                      | succ iyVal =>
                          cases n with
                          | zero =>
                              simp [eraseFin]
                              apply hrel 0 <;> simp
                          | succ n =>
                              simp [eraseFin]
                              apply ih htailLen
                              · intro k hkx hky
                                apply hrel (k + 1)
                                · simpa using Nat.succ_lt_succ hkx
                                · simpa using Nat.succ_lt_succ hky
                              · exact Nat.succ.inj hindex

theorem list_get_append_left {α : Type} (xs ys : List α)
    {i : Nat} (hi : i < xs.length)
    (happend : i < (xs ++ ys).length) :
    (xs ++ ys).get ⟨i, happend⟩ = xs.get ⟨i, hi⟩ := by
  change (xs ++ ys)[i] = xs[i]
  exact List.getElem_append_left hi

theorem list_get_append_right {α : Type} (xs ys : List α)
    {i : Nat} (hi : xs.length ≤ i)
    (happend : i < (xs ++ ys).length) :
    (xs ++ ys).get ⟨i, happend⟩ =
      ys.get ⟨i - xs.length, by
        have hlen : (xs ++ ys).length = xs.length + ys.length := by
          simp
        omega⟩ := by
  have hright : i - xs.length < ys.length := by
    have hlen : (xs ++ ys).length = xs.length + ys.length := by
      simp
    omega
  change (xs ++ ys)[i] = ys[i - xs.length]
  exact List.getElem_append_right hi

theorem list_get_append_single_at_length {α : Type}
    (xs ys : List α) (x : α) :
    (xs ++ x :: ys).get ⟨xs.length, by simp⟩ = x := by
  change (xs ++ x :: ys)[xs.length] = x
  simp

def listPrefixIndex {α : Type} {pref full suffix : List α}
    (hfull : full = pref ++ suffix) (i : Fin pref.length) :
    Fin full.length :=
  ⟨i.val, by
    rw [hfull]
    simp
    omega⟩

theorem listPrefixIndex_get {α : Type} {pref full suffix : List α}
    (hfull : full = pref ++ suffix) (i : Fin pref.length) :
    full.get (listPrefixIndex hfull i) = pref.get i := by
  have hbound : i.val < full.length := by
    rw [hfull]
    simp
    omega
  have hopt :
      full[i.val]? = pref[i.val]? := by
    rw [hfull]
    exact List.getElem?_append_left (l₁ := pref) (l₂ := suffix) i.isLt
  have hfullSome :
      full[i.val]? = some (full.get ⟨i.val, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  have hprefSome :
      pref[i.val]? = some (pref.get i) :=
    List.getElem?_eq_getElem i.isLt
  rw [hfullSome, hprefSome] at hopt
  injection hopt with hget

theorem listPrefixIndex_val {α : Type} {pref full suffix : List α}
    (hfull : full = pref ++ suffix) (i : Fin pref.length) :
    (listPrefixIndex hfull i).val = i.val :=
  rfl

theorem append_pointwise_relation {α β : Type} {R : α → β → Prop}
    {leftIds rightIds : List α} {leftLabels rightLabels : List β}
    (hleftLen : leftIds.length = leftLabels.length)
    (hrightLen : rightIds.length = rightLabels.length)
    (hleft :
      ∀ (n : Nat) (hid : n < leftIds.length)
        (hlabel : n < leftLabels.length),
        R (leftIds.get ⟨n, hid⟩) (leftLabels.get ⟨n, hlabel⟩))
    (hright :
      ∀ (n : Nat) (hid : n < rightIds.length)
        (hlabel : n < rightLabels.length),
        R (rightIds.get ⟨n, hid⟩) (rightLabels.get ⟨n, hlabel⟩))
    (n : Nat)
    (hid : n < (leftIds ++ rightIds).length)
    (hlabel : n < (leftLabels ++ rightLabels).length) :
    R ((leftIds ++ rightIds).get ⟨n, hid⟩)
      ((leftLabels ++ rightLabels).get ⟨n, hlabel⟩) := by
  by_cases hbefore : n < leftIds.length
  · have hbeforeLabel : n < leftLabels.length := by omega
    rw [list_get_append_left leftIds rightIds hbefore hid,
      list_get_append_left leftLabels rightLabels hbeforeLabel hlabel]
    exact hleft n hbefore hbeforeLabel
  · have hafter : leftIds.length ≤ n := Nat.le_of_not_gt hbefore
    have hafterLabel : leftLabels.length ≤ n := by omega
    rw [list_get_append_right leftIds rightIds hafter hid,
      list_get_append_right leftLabels rightLabels hafterLabel hlabel]
    have hright' :=
      hright (n - leftIds.length)
        (by
          have hlen : (leftIds ++ rightIds).length =
              leftIds.length + rightIds.length := by simp
          omega)
        (by
          have hlen : (leftLabels ++ rightLabels).length =
              leftLabels.length + rightLabels.length := by simp
          omega)
    simpa [hleftLen] using hright'

theorem map_eraseFin {α β : Type} (f : α → β) :
    ∀ (xs : List α) (i : Fin xs.length),
      (eraseFin xs i).map f =
        eraseFin (xs.map f) (Fin.cast (by simp) i)
  | [], i => nomatch i
  | _ :: xs, ⟨0, _⟩ => by
      change xs.map f = xs.map f
      rfl
  | x :: xs, ⟨n + 1, h⟩ => by
      have ih := map_eraseFin f xs ⟨n, Nat.lt_of_succ_lt_succ h⟩
      simp [eraseFin, ih]

theorem mem_of_mem_eraseFin {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length) {x : α},
      x ∈ eraseFin xs i → x ∈ xs
  | [], i, _x, _hmem => nomatch i
  | y :: _ys, ⟨0, _⟩, x, hmem => by
      right
      simpa [eraseFin] using hmem
  | y :: ys, ⟨n + 1, h⟩, x, hmem => by
      simp [eraseFin] at hmem
      rcases hmem with hxy | htail
      · simp [hxy]
      · have htailOrig :
            x ∈ ys :=
          mem_of_mem_eraseFin ys ⟨n, Nat.lt_of_succ_lt_succ h⟩ htail
        simp [htailOrig]

theorem mem_eraseFin_of_mem_ne_get {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length) {x : α},
      x ∈ xs → x ≠ xs.get i → x ∈ eraseFin xs i
  | [], i, _x, _hmem, _hne => nomatch i
  | _ :: xs, ⟨0, _⟩, x, hmem, hne => by
      simp at hmem
      rcases hmem with hhead | htail
      · exact False.elim (hne hhead)
      · simpa [eraseFin] using htail
  | y :: ys, ⟨n + 1, h⟩, x, hmem, hne => by
      simp [eraseFin]
      simp at hmem
      rcases hmem with hhead | htail
      · left
        exact hhead
      · right
        apply mem_eraseFin_of_mem_ne_get ys
          ⟨n, Nat.lt_of_succ_lt_succ h⟩ htail
        intro hget
        exact hne hget

theorem get_not_mem_eraseFin_of_nodup {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      xs.Nodup → xs.get i ∉ eraseFin xs i
  | [], i, _hnodup => nomatch i
  | head :: xs, ⟨0, _⟩, hnodup => by
      have hsplit : head ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      simpa [eraseFin] using hsplit.1
  | x :: xs, ⟨n + 1, h⟩, hnodup => by
      intro hmem
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      simp [eraseFin] at hmem
      rcases hmem with hhead | htail
      · exact hsplit.1 (by
          rw [← hhead]
          exact List.get_mem xs ⟨n, Nat.lt_of_succ_lt_succ h⟩)
      · exact get_not_mem_eraseFin_of_nodup xs
          ⟨n, Nat.lt_of_succ_lt_succ h⟩ hsplit.2 htail

theorem nodup_eraseFin {α : Type} :
    ∀ (xs : List α) (i : Fin xs.length),
      xs.Nodup → (eraseFin xs i).Nodup
  | [], i, _hnodup => nomatch i
  | head :: xs, ⟨0, _⟩, hnodup => by
      have hsplit : head ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      simpa [eraseFin] using hsplit.2
  | x :: xs, ⟨n + 1, h⟩, hnodup => by
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      have htail :
          (eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩).Nodup :=
        nodup_eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩ hsplit.2
      have hnot :
          x ∉ eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩ := by
        intro hmem
        exact hsplit.1
          (mem_of_mem_eraseFin xs ⟨n, Nat.lt_of_succ_lt_succ h⟩ hmem)
      simp [eraseFin, hnot, htail]

theorem eraseFin_eq_of_eq {α : Type} {xs ys : List α}
    (hxy : xs = ys) (i : Fin xs.length) :
    eraseFin xs i =
      eraseFin ys (Fin.cast (by rw [← hxy]) i) := by
  cases hxy
  simp

theorem nodup_append_of_nodup_disjoint {α : Type} :
    ∀ (xs ys : List α),
      xs.Nodup →
      ys.Nodup →
      (∀ x : α, x ∈ xs → x ∈ ys → False) →
        (xs ++ ys).Nodup
  | [], ys, _hxs, hys, _hdisjoint => by
      simpa
  | x :: xs, ys, hxs, hys, hdisjoint => by
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hxs
      constructor
      · intro a hmem heq
        simp at hmem
        rcases hmem with hmemXs | hmemYs
        · exact hsplit.1 (by simpa [heq] using hmemXs)
        · exact hdisjoint x (by simp) (by simpa [heq] using hmemYs)
      · exact nodup_append_of_nodup_disjoint xs ys hsplit.2 hys
          (by
            intro a hmemXs hmemYs
            exact hdisjoint a (by simp [hmemXs]) hmemYs)

theorem nodup_append_left {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).Nodup → xs.Nodup
  | [], _ys, _hnodup => by simp
  | head :: xs, ys, hnodup => by
      have hsplit : head ∉ xs ++ ys ∧ (xs ++ ys).Nodup := by
        simpa using hnodup
      exact List.nodup_cons.mpr
        ⟨by
          intro hmem
          exact hsplit.1 (by simp [hmem]),
         nodup_append_left xs ys hsplit.2⟩

theorem nodup_append_right {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).Nodup → ys.Nodup
  | [], ys, hnodup => by simpa using hnodup
  | head :: xs, ys, hnodup => by
      have hsplit : head ∉ xs ++ ys ∧ (xs ++ ys).Nodup := by
        simpa using hnodup
      exact nodup_append_right xs ys hsplit.2

theorem nodup_append_disjoint {α : Type} :
    ∀ (xs ys : List α) {x : α},
      (xs ++ ys).Nodup → x ∈ xs → x ∈ ys → False
  | [], _ys, _x, _hnodup, hleft, _hright => by cases hleft
  | head :: xs, ys, x, hnodup, hleft, hright => by
      have hsplit : head ∉ xs ++ ys ∧ (xs ++ ys).Nodup := by
        simpa using hnodup
      simp at hleft
      rcases hleft with hhead | htail
      · subst x
        exact hsplit.1 (by simp [hright])
      · exact nodup_append_disjoint xs ys hsplit.2 htail hright

theorem list_exists_get_of_mem {α : Type} {x : α} :
    ∀ (xs : List α), x ∈ xs → ∃ i : Fin xs.length, xs.get i = x
  | [], h => by cases h
  | y :: ys, h => by
      simp at h
      rcases h with h | h
      · refine ⟨⟨0, by simp⟩, ?_⟩
        simp [h]
      · rcases list_exists_get_of_mem ys h with ⟨i, hi⟩
        refine ⟨⟨i.val + 1, by simp [i.isLt]⟩, ?_⟩
        exact hi

theorem findSome?_exists_of_mem_isSome {α β : Type}
    (xs : List α) (f : α → Option β) {x : α}
    (hmem : x ∈ xs) (hxs : (f x).isSome) :
    ∃ y : β, xs.findSome? f = some y := by
  cases hfind : xs.findSome? f with
  | some y =>
      exact ⟨y, rfl⟩
  | none =>
      have hall := (List.findSome?_eq_none_iff).mp hfind
      have hxnone := hall x hmem
      rw [hxnone] at hxs
      simp at hxs

theorem list_mem_tail_of_mem_cons_ne {α : Type} {head x : α} {tail : List α}
    (hmem : x ∈ head :: tail) (hne : head ≠ x) : x ∈ tail := by
  simp at hmem
  rcases hmem with h | h
  · exact False.elim (hne h.symm)
  · exact h

theorem list_nodup_ofFn_injective {α : Type} {n : Nat}
    (f : Fin n → α) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.ofFn_succ]
      constructor
      · intro a hmem heq
        rw [List.mem_ofFn] at hmem
        rcases hmem with ⟨i, hi⟩
        have hidx : i.succ = (0 : Fin (n + 1)) :=
          hf (hi.trans heq.symm)
        exact False.elim ((Fin.succ_ne_zero i) hidx)
      · apply ih
        intro i j hij
        have hidx : i.succ = j.succ := hf hij
        exact (Fin.succ_inj.mp hidx)

theorem list_ofFn_get {α : Type} (xs : List α) :
    List.ofFn (fun i : Fin xs.length => xs.get i) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [List.getElem_ofFn]

theorem list_nodup_of_get_injective {α : Type} (xs : List α)
    (hf : Function.Injective fun i : Fin xs.length => xs.get i) :
    xs.Nodup := by
  have hnodup :
      (List.ofFn (fun i : Fin xs.length => xs.get i)).Nodup :=
    list_nodup_ofFn_injective
      (fun i : Fin xs.length => xs.get i) hf
  rw [list_ofFn_get xs] at hnodup
  exact hnodup

theorem list_get_injective_of_nodup {α : Type} :
    ∀ (xs : List α), xs.Nodup →
      Function.Injective fun i : Fin xs.length => xs.get i
  | [], _hnodup, i, _j, _h => by
      cases i with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | x :: xs, hnodup, i, j, h => by
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      cases i with
      | mk iVal iLt =>
          cases j with
          | mk jVal jLt =>
              cases iVal with
              | zero =>
                  cases jVal with
                  | zero => rfl
                  | succ jVal =>
                      have hmem :
                          xs.get ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩ ∈ xs :=
                        List.get_mem xs ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩
                      have hx :
                          x = xs.get
                            ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩ := by
                        simpa using h
                      exact False.elim (hsplit.1 (hx ▸ hmem))
              | succ iVal =>
                  cases jVal with
                  | zero =>
                      have hmem :
                          xs.get ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩ ∈ xs :=
                        List.get_mem xs ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩
                      have hx :
                          xs.get
                            ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩ = x := by
                        simpa using h
                      exact False.elim (hsplit.1 (hx.symm ▸ hmem))
                  | succ jVal =>
                      have htail :
                          (⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩ :
                              Fin xs.length) =
                            ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩ := by
                        apply list_get_injective_of_nodup xs hsplit.2
                        simpa using h
                      apply Fin.ext
                      have hval : iVal = jVal := congrArg Fin.val htail
                      exact congrArg Nat.succ hval

theorem list_length_le_of_nodup_subset {α : Type} :
    ∀ (xs ys : List α),
      xs.Nodup →
      (∀ x : α, x ∈ xs → x ∈ ys) →
        xs.length ≤ ys.length
  | [], ys, _hnodup, _hsubset => by
      simp
  | x :: xs, ys, hnodup, hsubset => by
      have hxmem : x ∈ ys := hsubset x (by simp)
      rcases list_exists_get_of_mem ys hxmem with ⟨i, hi⟩
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      have htailSubset :
          ∀ y : α, y ∈ xs → y ∈ eraseFin ys i := by
        intro y hy
        apply mem_eraseFin_of_mem_ne_get ys i
        · exact hsubset y (by simp [hy])
        · intro hyi
          exact hsplit.1 (by
            rw [hyi, hi] at hy
            exact hy)
      have ih :=
        list_length_le_of_nodup_subset xs (eraseFin ys i)
          hsplit.2 htailSubset
      have hlen := eraseFin_length ys i
      rw [hlen] at ih
      have hysPos : 0 < ys.length :=
        Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      have hsucc : xs.length + 1 ≤ (ys.length - 1) + 1 :=
        Nat.succ_le_succ ih
      have hsub : ys.length - 1 + 1 = ys.length :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hysPos)
      simpa [hsub] using hsucc

theorem list_length_le_fin_of_nodup {n : Nat}
    (xs : List (Fin n)) (hnodup : xs.Nodup) :
    xs.length ≤ n := by
  have hsubset :
      ∀ x : Fin n, x ∈ xs → x ∈ List.finRange n := by
    intro x _hx
    exact List.mem_finRange x
  have hle :=
    list_length_le_of_nodup_subset xs (List.finRange n) hnodup hsubset
  simpa [List.length_ofFn, List.finRange] using hle

/--
A typed ordered-port string-diagram signature.

`Edge` is the label carried by wires/edges.  `Port` is the label carried by
open frontier endpoints.  Unoriented signatures usually take `Port` to be the
same type as `Edge`.  Oriented signatures usually take `Port` to be a direction
paired with an edge type.  `portEdge` forgets endpoint-only data,
`compatible` states when two frontier endpoints may be joined, and
`compatible_edge` and `compatible_symm` ensure such a connection has one edge
label and can be viewed from either endpoint.

Each node label has a finite ordered list of ports, represented by `arity` and
`port`.  The order is part of the formal data because the canonical traversal
and linear isomorphism test depend on it.
-/
structure Signature where
  Edge : Type
  Port : Type
  Node : Type
  portEdge : Port → Edge
  arity : Node → Nat
  port : (node : Node) → Fin (arity node) → Port
  compatible : Port → Port → Prop
  compatible_edge :
    ∀ {left right : Port}, compatible left right → portEdge left = portEdge right
  compatible_symm :
    ∀ {left right : Port}, compatible left right → compatible right left

namespace Unoriented

/-- Build an unoriented signature: endpoint compatibility is equality of wire
types, while every constructor still has an ordered list of typed ports. -/
def signature (Ty Node : Type)
    (arity : Node → Nat)
    (portTy : (node : Node) → Fin (arity node) → Ty) :
    Signature where
  Edge := Ty
  Port := Ty
  Node := Node
  portEdge := id
  arity := arity
  port := portTy
  compatible := Eq
  compatible_edge := by
    intro left right h
    exact h
  compatible_symm := by
    intro left right h
    exact h.symm

end Unoriented

/-- Endpoint polarity for oriented string diagrams. -/
inductive Direction where
  | input
  | output
deriving DecidableEq, Repr

namespace Direction

def opposite : Direction → Direction
  | .input => .output
  | .output => .input

@[simp]
theorem opposite_opposite (d : Direction) : opposite (opposite d) = d := by
  cases d <;> rfl

end Direction

namespace Oriented

/-- A typed oriented endpoint. -/
structure Endpoint (Ty : Type) where
  direction : Direction
  ty : Ty
deriving Repr

/-- Build an oriented signature.  Two endpoints are compatible when their wire
types agree and their directions are opposite. -/
def signature (Ty Node : Type)
    (arity : Node → Nat)
    (portSpec : (node : Node) → Fin (arity node) → Endpoint Ty) :
    Signature where
  Edge := Ty
  Port := Endpoint Ty
  Node := Node
  portEdge := fun p => p.ty
  arity := arity
  port := portSpec
  compatible := fun p q =>
    p.ty = q.ty ∧ Direction.opposite p.direction = q.direction
  compatible_edge := by
    intro left right h
    exact h.1
  compatible_symm := by
    intro left right h
    constructor
    · exact h.1.symm
    · rw [← h.2]
      exact Direction.opposite_opposite left.direction

end Oriented

/-- Constructor tags for the traversal grammar. -/
inductive Ctor where
  | finish
  | connect
  | bud
deriving DecidableEq, Repr

namespace Signature

variable (Sig : Signature)

theorem edge_eq_of_compatible {left right : Sig.Port}
    (ok : Sig.compatible left right) :
    Sig.portEdge left = Sig.portEdge right :=
  Sig.compatible_edge ok

theorem compatible_comm {left right : Sig.Port}
    (ok : Sig.compatible left right) :
    Sig.compatible right left :=
  Sig.compatible_symm ok

def nodePorts (node : Sig.Node) : List Sig.Port :=
  List.ofFn fun slot : Fin (Sig.arity node) => Sig.port node slot

def nodePortsExcept (node : Sig.Node) (entry : Fin (Sig.arity node)) :
    List Sig.Port :=
  eraseFin (Sig.nodePorts node) (Fin.cast (by simp [nodePorts]) entry)

end Signature

/--
Canonical traversal syntax for typed open string diagrams.

The index is the ordered frontier boundary.  `connect` always processes the
first frontier port and connects it to one later frontier port.  `bud` processes
the first frontier port by entering an ordered constructor port and appending
the remaining constructor ports, in constructor order, to the frontier.
-/
inductive Diag (Sig : Signature) : List Sig.Port → Type
  | finish : Diag Sig []
  | connect {active : Sig.Port} {frontier : List Sig.Port}
      (mate : Fin frontier.length)
      (ok : Sig.compatible active (frontier.get mate))
      (child : Diag Sig (eraseFin frontier mate)) :
      Diag Sig (active :: frontier)
  | bud {active : Sig.Port} {frontier : List Sig.Port}
      (node : Sig.Node)
      (entry : Fin (Sig.arity node))
      (ok : Sig.compatible active (Sig.port node entry))
      (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry)) :
      Diag Sig (active :: frontier)

namespace Diag

variable {Sig : Signature}

/-- Structural rank used for the generated syntax coding. -/
def rank : ∀ {boundary : List Sig.Port}, Diag Sig boundary → Nat
  | _, finish => 0
  | _, connect _ _ child => rank child + 1
  | _, bud _ _ _ child => rank child + 1

/-- Transport a `bud` constructor across equal constructor labels and equal
entry positions, with the child transported along the induced frontier
equality. -/
theorem bud_transport
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {nodeA nodeB : Sig.Node}
    {entryA : Fin (Sig.arity nodeA)} {entryB : Fin (Sig.arity nodeB)}
    (hnode : nodeB = nodeA)
    (hentryVal : entryB.val = entryA.val)
    (okA : Sig.compatible activeLabel (Sig.port nodeA entryA))
    (okB : Sig.compatible activeLabel (Sig.port nodeB entryB))
    (childA : Diag Sig (frontier ++ Sig.nodePortsExcept nodeA entryA))
    (childB : Diag Sig (frontier ++ Sig.nodePortsExcept nodeB entryB))
    (hfrontier :
      frontier ++ Sig.nodePortsExcept nodeB entryB =
        frontier ++ Sig.nodePortsExcept nodeA entryA)
    (hchild : childA = hfrontier ▸ childB) :
    Diag.bud nodeA entryA okA childA =
      Diag.bud nodeB entryB okB childB := by
  cases hnode
  have hentry : entryB = entryA := Fin.ext hentryVal
  cases hentry
  cases hfrontier
  have hok : okB = okA := Subsingleton.elim _ _
  cases hok
  exact congrArg (fun child => Diag.bud nodeA entryA okA child) hchild

end Diag

/-- An edge recorded by the concrete traversal renderer. -/
structure RenderEdge (Sig : Signature) where
  label : Sig.Edge
  leftLabel : Sig.Port
  rightLabel : Sig.Port
  left : Nat
  right : Nat
  left_label : Sig.portEdge leftLabel = label
  right_label : Sig.portEdge rightLabel = label
  compatible : Sig.compatible leftLabel rightLabel

/-- A constructor node recorded by the concrete traversal renderer. -/
structure RenderNode (Sig : Signature) where
  label : Sig.Node
  incident : List Nat

/--
Mutable-by-return construction state for rendering traversal syntax.

The `frontierIds` field stores endpoint identifiers in the same order as the
frontier in the type index.  `connect` consumes the head identifier and one
later identifier.  `bud` consumes the head identifier, allocates the ordered
constructor endpoints, connects the chosen entry endpoint, and appends the
remaining constructor endpoints to the frontier.
-/
structure RenderState (Sig : Signature) (frontier : List Sig.Port) where
  nextEndpoint : Nat
  endpoints : List Sig.Port
  edges : List (RenderEdge Sig)
  nodes : List (RenderNode Sig)
  frontierIds : List Nat
  frontierIds_length : frontierIds.length = frontier.length

namespace RenderState

variable (Sig : Signature)

def initial (boundary : List Sig.Port) : RenderState Sig boundary where
  nextEndpoint := boundary.length
  endpoints := boundary
  edges := []
  nodes := []
  frontierIds := List.range boundary.length
  frontierIds_length := by simp

theorem frontierIds_ne_nil {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    (st : RenderState Sig (active :: frontier)) :
    st.frontierIds ≠ [] := by
  intro hids
  have hlen := st.frontierIds_length
  rw [hids] at hlen
  simp at hlen

/--
ID-level validity for a renderer state.  It is the proof layer that turns the
raw `Nat` endpoint identifiers stored in the trace into valid finite endpoint
indices with the labels required by semantic evidence.
-/
structure ValidIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  nextEndpoint_eq : st.nextEndpoint = st.endpoints.length
  frontier_bound :
    ∀ id : Nat, id ∈ st.frontierIds → id < st.endpoints.length
  frontier_label :
    ∀ (n : Nat) (hid : n < st.frontierIds.length)
      (hfrontier : n < frontier.length),
      st.endpoints.get
        ⟨st.frontierIds.get ⟨n, hid⟩,
          frontier_bound (st.frontierIds.get ⟨n, hid⟩)
            (List.get_mem st.frontierIds ⟨n, hid⟩)⟩ =
      frontier.get ⟨n, hfrontier⟩
  edge_left_bound :
    ∀ edge : RenderEdge Sig, edge ∈ st.edges → edge.left < st.endpoints.length
  edge_right_bound :
    ∀ edge : RenderEdge Sig, edge ∈ st.edges → edge.right < st.endpoints.length
  edge_left_label :
    ∀ (edge : RenderEdge Sig) (hmem : edge ∈ st.edges),
      st.endpoints.get ⟨edge.left, edge_left_bound edge hmem⟩ =
        edge.leftLabel
  edge_right_label :
    ∀ (edge : RenderEdge Sig) (hmem : edge ∈ st.edges),
      st.endpoints.get ⟨edge.right, edge_right_bound edge hmem⟩ =
        edge.rightLabel
  node_incident_length :
    ∀ node : RenderNode Sig, node ∈ st.nodes →
      node.incident.length = Sig.arity node.label
  node_incident_bound :
    ∀ (node : RenderNode Sig) (_hmem : node ∈ st.nodes)
      (slot : Fin node.incident.length),
      node.incident.get slot < st.endpoints.length
  node_incident_label :
    ∀ (node : RenderNode Sig) (hmem : node ∈ st.nodes)
      (slot : Fin node.incident.length),
      st.endpoints.get
        ⟨node.incident.get slot,
          node_incident_bound node hmem slot⟩ =
        Sig.port node.label
          (Fin.cast (node_incident_length node hmem) slot)

def edgeEndpointIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : List Nat :=
  st.edges.flatMap fun edge => [edge.left, edge.right]

/--
The endpoint-consumption invariant for renderer states.  Every endpoint ID is
either pending in the ordered frontier or has already been consumed by exactly
one rendered edge endpoint.  This is the invariant from which the semantic
`endpointEdge` map is later derived when the frontier is empty.
-/
structure EndpointPartition {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  frontier_nodup : st.frontierIds.Nodup
  consumed_nodup : st.edgeEndpointIds.Nodup
  consumed_bound :
    ∀ id : Nat, id ∈ st.edgeEndpointIds → id < st.endpoints.length
  frontier_consumed_disjoint :
    ∀ id : Nat, id ∈ st.frontierIds → id ∈ st.edgeEndpointIds → False
  endpoint_covered :
    ∀ id : Nat, id < st.endpoints.length →
      id ∈ st.frontierIds ∨ id ∈ st.edgeEndpointIds

/-- Every rendered constructor node stores each incident endpoint at most once. -/
structure NodeIncidentNodup {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : Prop where
  node_incident_nodup :
    ∀ node : RenderNode Sig, node ∈ st.nodes → node.incident.Nodup

def nodeIncidentIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) : List Nat :=
  st.nodes.flatMap fun node => node.incident

def ownerEndpointIds {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundary : List Sig.Port) : List Nat :=
  List.range boundary.length ++ st.nodeIncidentIds

/--
Endpoint-ID inventory for semantic owners.  Boundary positions own the initial
range of endpoint IDs, and rendered constructor nodes own their ordered
incident IDs.
-/
structure OwnerIdPartition {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundary : List Sig.Port) : Prop where
  owner_nodup : (st.ownerEndpointIds boundary).Nodup
  owner_bound :
    ∀ id : Nat, id ∈ st.ownerEndpointIds boundary → id < st.endpoints.length
  owner_covered :
    ∀ id : Nat, id < st.endpoints.length → id ∈ st.ownerEndpointIds boundary

theorem OwnerIdPartition.boundaryIds_nodup
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (List.range boundary.length).Nodup :=
  nodup_append_left (List.range boundary.length) st.nodeIncidentIds
    (by simpa [ownerEndpointIds] using ho.owner_nodup)

theorem OwnerIdPartition.nodeIncidentIds_nodup
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    st.nodeIncidentIds.Nodup :=
  nodup_append_right (List.range boundary.length) st.nodeIncidentIds
    (by simpa [ownerEndpointIds] using ho.owner_nodup)

theorem OwnerIdPartition.boundary_nodeIncidentIds_disjoint
    {Sig : Signature} {frontier : List Sig.Port}
    {st : RenderState Sig frontier} {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) {id : Nat}
    (hboundary : id ∈ List.range boundary.length)
    (hnode : id ∈ st.nodeIncidentIds) : False :=
  nodup_append_disjoint (List.range boundary.length) st.nodeIncidentIds
    (by simpa [ownerEndpointIds] using ho.owner_nodup) hboundary hnode

/-- `base` occurs as the ordered prefix of a renderer state's endpoint list. -/
structure EndpointPrefix {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (base : List Sig.Port) where
  suffix : List Sig.Port
  endpoints_eq : st.endpoints = base ++ suffix

def EndpointPrefix.trans {Sig : Signature}
    {frontier frontier' : List Sig.Port}
    {st : RenderState Sig frontier} {st' : RenderState Sig frontier'}
    {base : List Sig.Port}
    (pref : EndpointPrefix st base)
    (next : EndpointPrefix st' st.endpoints) :
    EndpointPrefix st' base :=
  match pref, next with
  | ⟨prefSuffix, hpref⟩, ⟨nextSuffix, hnext⟩ =>
      { suffix := prefSuffix ++ nextSuffix
        endpoints_eq := by
          calc
            st'.endpoints = st.endpoints ++ nextSuffix := hnext
            _ = (base ++ prefSuffix) ++ nextSuffix := by
              exact congrArg (fun endpoints => endpoints ++ nextSuffix) hpref
            _ = base ++ (prefSuffix ++ nextSuffix) := by
              rw [List.append_assoc] }

/-- Ordered boundary evidence derived from a renderer endpoint-prefix proof. -/
structure BoundaryEvidence {Sig : Signature}
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  boundaryPort : Fin boundary.length → Fin st.endpoints.length
  boundary_injective : Function.Injective boundaryPort
  boundary_label :
    ∀ b : Fin boundary.length,
      st.endpoints.get (boundaryPort b) = boundary.get b

def boundaryEvidenceOfPrefix {Sig : Signature} {st : RenderState Sig []}
    {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary) :
    BoundaryEvidence st boundary where
  boundaryPort := fun b =>
    ⟨b.val, by
      rw [pref.endpoints_eq]
      simp
      omega⟩
  boundary_injective := by
    intro left right h
    apply Fin.ext
    change left.val = right.val
    exact congrArg (fun x : Fin st.endpoints.length => x.val) h
  boundary_label := by
    intro b
    have hbound : b.val < st.endpoints.length := by
      rw [pref.endpoints_eq]
      simp
      omega
    change st.endpoints[b.val]'hbound = boundary[b.val]
    have hopt : st.endpoints[b.val]? = boundary[b.val]? := by
      rw [pref.endpoints_eq]
      exact List.getElem?_append_left (l₁ := boundary)
        (l₂ := pref.suffix) b.isLt
    have hstSome :
        st.endpoints[b.val]? = some (st.endpoints[b.val]'hbound) :=
      List.getElem?_eq_getElem hbound
    have hboundarySome :
        boundary[b.val]? = some boundary[b.val] :=
      List.getElem?_eq_getElem b.isLt
    rw [hstSome, hboundarySome] at hopt
    simpa using hopt

theorem boundaryEvidenceOfPrefix_boundaryPort_val {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary) (b : Fin boundary.length) :
    ((boundaryEvidenceOfPrefix pref).boundaryPort b).val = b.val :=
  rfl

theorem boundaryEvidenceOfPrefix_exists_of_boundary_id {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary)
    (endpoint : Fin st.endpoints.length)
    (hboundary : endpoint.val ∈ List.range boundary.length) :
    ∃ b : Fin boundary.length,
      (boundaryEvidenceOfPrefix pref).boundaryPort b = endpoint := by
  let b : Fin boundary.length := ⟨endpoint.val, List.mem_range.mp hboundary⟩
  refine ⟨b, ?_⟩
  apply Fin.ext
  simp [b, boundaryEvidenceOfPrefix_boundaryPort_val pref b]

theorem initial_validIds {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).ValidIds where
  nextEndpoint_eq := by
    simp [initial]
  frontier_bound := by
    intro id hid
    simpa [initial] using hid
  frontier_label := by
    intro n hid hfrontier
    simp [initial]
  edge_left_bound := by
    intro edge hmem
    simp [initial] at hmem
  edge_right_bound := by
    intro edge hmem
    simp [initial] at hmem
  edge_left_label := by
    intro edge hmem
    simp [initial] at hmem
  edge_right_label := by
    intro edge hmem
    simp [initial] at hmem
  node_incident_length := by
    intro node hmem
    simp [initial] at hmem
  node_incident_bound := by
    intro node hmem slot
    simp [initial] at hmem
  node_incident_label := by
    intro node hmem slot
    simp [initial] at hmem

theorem initial_endpointPartition {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).EndpointPartition where
  frontier_nodup := by
    simp [initial, List.nodup_range]
  consumed_nodup := by
    simp [edgeEndpointIds, initial]
  consumed_bound := by
    intro id hmem
    simp [edgeEndpointIds, initial] at hmem
  frontier_consumed_disjoint := by
    intro id hfrontier hconsumed
    simp [edgeEndpointIds, initial] at hconsumed
  endpoint_covered := by
    intro id hid
    left
    simpa [initial] using (List.mem_range.mpr hid)

theorem initial_nodeIncidentNodup {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).NodeIncidentNodup where
  node_incident_nodup := by
    intro node hmem
    simp [initial] at hmem

theorem initial_ownerIdPartition {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).OwnerIdPartition boundary where
  owner_nodup := by
    simp [ownerEndpointIds, nodeIncidentIds, initial, List.nodup_range]
  owner_bound := by
    intro id hmem
    simpa [ownerEndpointIds, nodeIncidentIds, initial] using hmem
  owner_covered := by
    intro id hid
    simpa [ownerEndpointIds, nodeIncidentIds, initial] using
      (List.mem_range.mpr hid)

theorem EndpointPartition.endpoint_consumed_of_frontier_empty
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    endpoint.val ∈ st.edgeEndpointIds := by
  have hfrontierIds : st.frontierIds = [] := by
    cases hids : st.frontierIds with
    | nil => rfl
    | cons head tail =>
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simp at hlen
  rcases hp.endpoint_covered endpoint.val endpoint.isLt with hfrontier | hconsumed
  · rw [hfrontierIds] at hfrontier
    cases hfrontier
  · exact hconsumed

def edgeEndpointIdsOfEdges {Sig : Signature}
    (edges : List (RenderEdge Sig)) : List Nat :=
  edges.flatMap fun edge => [edge.left, edge.right]

theorem edgeEndpointIdsOfEdges_tail_nodup
    {Sig : Signature}
    (edge : RenderEdge Sig) (edges : List (RenderEdge Sig))
    (hnodup : (edgeEndpointIdsOfEdges (edge :: edges)).Nodup) :
    (edgeEndpointIdsOfEdges edges).Nodup := by
  simp [edgeEndpointIdsOfEdges] at hnodup
  exact hnodup.2.2

theorem edgeEndpointIdsOfEdges_left_not_tail
    {Sig : Signature}
    (edge : RenderEdge Sig) (edges : List (RenderEdge Sig))
    (hnodup : (edgeEndpointIdsOfEdges (edge :: edges)).Nodup) :
    edge.left ∉ edgeEndpointIdsOfEdges edges := by
  intro hmem
  simp [edgeEndpointIdsOfEdges] at hnodup hmem
  rcases hmem with ⟨edge', hmem, hleft | hright⟩
  · exact (hnodup.1.2 edge' hmem).1 hleft
  · exact (hnodup.1.2 edge' hmem).2 hright

theorem edgeEndpointIdsOfEdges_right_not_tail
    {Sig : Signature}
    (edge : RenderEdge Sig) (edges : List (RenderEdge Sig))
    (hnodup : (edgeEndpointIdsOfEdges (edge :: edges)).Nodup) :
    edge.right ∉ edgeEndpointIdsOfEdges edges := by
  intro hmem
  simp [edgeEndpointIdsOfEdges] at hnodup hmem
  rcases hmem with ⟨edge', hmem, hleft | hright⟩
  · exact (hnodup.2.1 edge' hmem).1 hleft
  · exact (hnodup.2.1 edge' hmem).2 hright

theorem edgeEndpointIdsOfEdges_mem_left
    {Sig : Signature}
    (edges : List (RenderEdge Sig)) (edgeIndex : Fin edges.length) :
    (edges.get edgeIndex).left ∈ edgeEndpointIdsOfEdges edges := by
  simp [edgeEndpointIdsOfEdges]
  exact ⟨edges.get edgeIndex, List.get_mem edges edgeIndex, Or.inl rfl⟩

theorem edgeEndpointIdsOfEdges_mem_right
    {Sig : Signature}
    (edges : List (RenderEdge Sig)) (edgeIndex : Fin edges.length) :
    (edges.get edgeIndex).right ∈ edgeEndpointIdsOfEdges edges := by
  simp [edgeEndpointIdsOfEdges]
  exact ⟨edges.get edgeIndex, List.get_mem edges edgeIndex, Or.inr rfl⟩

theorem edgeEndpointIdsOfEdges_get_left_ne_right
    {Sig : Signature} :
    ∀ (edges : List (RenderEdge Sig)),
      (edgeEndpointIdsOfEdges edges).Nodup →
        ∀ edgeIndex : Fin edges.length,
          (edges.get edgeIndex).left ≠ (edges.get edgeIndex).right
  | [], _hnodup, edgeIndex => by
      cases edgeIndex with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | edge :: edges, hnodup, edgeIndex => by
      cases edgeIndex with
      | mk idx idxLt =>
          cases idx with
          | zero =>
              simp [edgeEndpointIdsOfEdges] at hnodup
              exact hnodup.1.1
          | succ idx =>
              have tailIndex : Fin edges.length :=
                ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩
              have hget :
                  (edge :: edges).get ⟨idx + 1, idxLt⟩ =
                    edges.get ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩ := rfl
              rw [hget]
              exact edgeEndpointIdsOfEdges_get_left_ne_right edges
                (edgeEndpointIdsOfEdges_tail_nodup edge edges hnodup)
                ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩

/--
Find the rendered edge that consumed an endpoint ID.  The input membership is
the consumed side of `EndpointPartition`, not a raw-ID guess.
-/
def edgeEndpointRefOfEndpointId {Sig : Signature} :
    ∀ (edges : List (RenderEdge Sig)) {id : Nat},
      id ∈ edgeEndpointIdsOfEdges edges →
        { edge : Fin edges.length //
          id = (edges.get edge).left ∨ id = (edges.get edge).right }
  | [], _id, hmem => by
      simp [edgeEndpointIdsOfEdges] at hmem
  | edge :: edges, id, hmem => by
      by_cases hleft : id = edge.left
      · exact ⟨⟨0, by simp⟩, Or.inl hleft⟩
      · by_cases hright : id = edge.right
        · exact ⟨⟨0, by simp⟩, Or.inr hright⟩
        · have hmemAppend :
              id ∈ [edge.left, edge.right] ++ edgeEndpointIdsOfEdges edges := by
            simpa [edgeEndpointIdsOfEdges] using hmem
          have htail : id ∈ edgeEndpointIdsOfEdges edges := by
            rcases List.mem_append.mp hmemAppend with hhead | htail
            · simp at hhead
              rcases hhead with hleft' | hright'
              · exact False.elim (hleft hleft')
              · exact False.elim (hright hright')
            · exact htail
          rcases edgeEndpointRefOfEndpointId edges htail with
            ⟨edgeIndex, hside⟩
          refine ⟨⟨edgeIndex.val + 1, by simp [edgeIndex.isLt]⟩, ?_⟩
          simpa using hside

theorem edgeEndpointRefOfEndpointId_unique {Sig : Signature} :
    ∀ (edges : List (RenderEdge Sig)) {id : Nat}
      (hmem : id ∈ edgeEndpointIdsOfEdges edges)
      (_hnodup : (edgeEndpointIdsOfEdges edges).Nodup)
      (edgeIndex : Fin edges.length),
      (id = (edges.get edgeIndex).left ∨
        id = (edges.get edgeIndex).right) →
        (edgeEndpointRefOfEndpointId edges hmem).1 = edgeIndex
  | [], _id, _hmem, _hnodup, edgeIndex, _hside => by
      cases edgeIndex with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | edge :: edges, id, hmem, hnodup, edgeIndex, hside => by
      cases edgeIndex with
      | mk idx idxLt =>
          cases idx with
          | zero =>
              simp at hside
              unfold edgeEndpointRefOfEndpointId
              rcases hside with hleftSide | hrightSide
              · simp [hleftSide]
              · by_cases hsame : edge.right = edge.left
                · simp [hrightSide, hsame]
                · simp [hrightSide, hsame]
          | succ idx =>
              let tailIndex : Fin edges.length :=
                ⟨idx, Nat.lt_of_succ_lt_succ idxLt⟩
              have hsideTail :
                  id = (edges.get tailIndex).left ∨
                    id = (edges.get tailIndex).right := by
                simpa [tailIndex] using hside
              unfold edgeEndpointRefOfEndpointId
              by_cases hleft : id = edge.left
              · have htailMem : edge.left ∈ edgeEndpointIdsOfEdges edges := by
                  rw [← hleft]
                  rcases hsideTail with htailLeft | htailRight
                  · rw [htailLeft]
                    exact edgeEndpointIdsOfEdges_mem_left edges tailIndex
                  · rw [htailRight]
                    exact edgeEndpointIdsOfEdges_mem_right edges tailIndex
                exact False.elim
                  (edgeEndpointIdsOfEdges_left_not_tail edge edges hnodup
                    htailMem)
              · by_cases hright : id = edge.right
                · have htailMem :
                      edge.right ∈ edgeEndpointIdsOfEdges edges := by
                    rw [← hright]
                    rcases hsideTail with htailLeft | htailRight
                    · rw [htailLeft]
                      exact edgeEndpointIdsOfEdges_mem_left edges tailIndex
                    · rw [htailRight]
                      exact edgeEndpointIdsOfEdges_mem_right edges tailIndex
                  exact False.elim
                    (edgeEndpointIdsOfEdges_right_not_tail edge edges hnodup
                      htailMem)
                · simp [hleft, hright]
                  have hmemTail : id ∈ edgeEndpointIdsOfEdges edges := by
                    simp [edgeEndpointIdsOfEdges] at hmem
                    rcases hmem with hleftMem | hrightMem | htail
                    · exact False.elim (hleft hleftMem)
                    · exact False.elim (hright hrightMem)
                    · simpa [edgeEndpointIdsOfEdges] using htail
                  have huniq :=
                    edgeEndpointRefOfEndpointId_unique edges hmemTail
                      (edgeEndpointIdsOfEdges_tail_nodup edge edges hnodup)
                      tailIndex hsideTail
                  simpa [tailIndex] using congrArg Fin.val huniq

def endpointEdgeOfPartition {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) : Fin st.edges.length :=
  (edgeEndpointRefOfEndpointId st.edges (id := endpoint.val) (by
    have hconsumed :=
      EndpointPartition.endpoint_consumed_of_frontier_empty hp endpoint
    simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hconsumed)).1

theorem endpointEdgeOfPartition_endpoint
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    endpoint.val =
        (st.edges.get (endpointEdgeOfPartition hp endpoint)).left ∨
      endpoint.val =
        (st.edges.get (endpointEdgeOfPartition hp endpoint)).right := by
  unfold endpointEdgeOfPartition
  have hconsumed :=
    EndpointPartition.endpoint_consumed_of_frontier_empty hp endpoint
  exact
    (edgeEndpointRefOfEndpointId st.edges (id := endpoint.val) (by
      simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hconsumed)).2

theorem endpointEdgeOfPartition_label
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length) :
    Sig.portEdge (st.endpoints.get endpoint) =
      (st.edges.get (endpointEdgeOfPartition hp endpoint)).label := by
  let edgeIndex := endpointEdgeOfPartition hp endpoint
  let edge := st.edges.get edgeIndex
  have hedgeMem : edge ∈ st.edges := List.get_mem st.edges edgeIndex
  have hside : endpoint.val = edge.left ∨ endpoint.val = edge.right := by
    simpa [edgeIndex, edge] using
      endpointEdgeOfPartition_endpoint hp endpoint
  change Sig.portEdge (st.endpoints.get endpoint) = edge.label
  rcases hside with hleft | hright
  · have hfin : endpoint = ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩ := by
      apply Fin.ext
      exact hleft
    calc
      Sig.portEdge (st.endpoints.get endpoint) =
          Sig.portEdge
            (st.endpoints.get
              ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩) := by
        rw [hfin]
      _ = Sig.portEdge edge.leftLabel := by
        rw [hv.edge_left_label edge hedgeMem]
      _ = edge.label := edge.left_label
  · have hfin : endpoint = ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩ := by
      apply Fin.ext
      exact hright
    calc
      Sig.portEdge (st.endpoints.get endpoint) =
          Sig.portEdge
            (st.endpoints.get
              ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩) := by
        rw [hfin]
      _ = Sig.portEdge edge.rightLabel := by
        rw [hv.edge_right_label edge hedgeMem]
      _ = edge.label := edge.right_label

theorem endpointEdgeOfPartition_eq_of_endpoint_side
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (endpoint : Fin st.endpoints.length)
    (edgeIndex : Fin st.edges.length)
    (hside : endpoint.val = (st.edges.get edgeIndex).left ∨
      endpoint.val = (st.edges.get edgeIndex).right) :
    endpointEdgeOfPartition hp endpoint = edgeIndex := by
  unfold endpointEdgeOfPartition
  apply edgeEndpointRefOfEndpointId_unique
  · simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hp.consumed_nodup
  · exact hside

theorem endpointEdgeOfPartition_left
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        ⟨(st.edges.get edgeIndex).left,
          hv.edge_left_bound (st.edges.get edgeIndex)
            (List.get_mem st.edges edgeIndex)⟩ = edgeIndex := by
  apply endpointEdgeOfPartition_eq_of_endpoint_side
  exact Or.inl rfl

theorem endpointEdgeOfPartition_right
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    endpointEdgeOfPartition hp
        ⟨(st.edges.get edgeIndex).right,
          hv.edge_right_bound (st.edges.get edgeIndex)
            (List.get_mem st.edges edgeIndex)⟩ = edgeIndex := by
  apply endpointEdgeOfPartition_eq_of_endpoint_side
  exact Or.inr rfl

theorem edge_left_ne_right_of_partition
    {Sig : Signature} {st : RenderState Sig []}
    (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    (st.edges.get edgeIndex).left ≠ (st.edges.get edgeIndex).right :=
  edgeEndpointIdsOfEdges_get_left_ne_right st.edges
    (by simpa [edgeEndpointIds, edgeEndpointIdsOfEdges] using hp.consumed_nodup)
    edgeIndex

theorem edgeCompatibleOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (left right : Fin st.endpoints.length)
    (hsame : endpointEdgeOfPartition hp left = endpointEdgeOfPartition hp right)
    (hne : left ≠ right) :
    Sig.compatible (st.endpoints.get left) (st.endpoints.get right) := by
  let edgeIndex := endpointEdgeOfPartition hp left
  let edge := st.edges.get edgeIndex
  have hedgeMem : edge ∈ st.edges := List.get_mem st.edges edgeIndex
  have hleftSide : left.val = edge.left ∨ left.val = edge.right := by
    simpa [edgeIndex, edge] using endpointEdgeOfPartition_endpoint hp left
  have hrightEdge : endpointEdgeOfPartition hp right = edgeIndex := by
    exact hsame.symm
  have hrightSide : right.val = edge.left ∨ right.val = edge.right := by
    have hraw := endpointEdgeOfPartition_endpoint hp right
    simpa [edgeIndex, edge, hrightEdge] using hraw
  rcases hleftSide with hleftL | hleftR
  · rcases hrightSide with hrightL | hrightR
    · have hfin : left = right := by
        apply Fin.ext
        exact hleftL.trans hrightL.symm
      exact False.elim (hne hfin)
    · have hleftFin :
          left = ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hleftL
      have hrightFin :
          right = ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hrightR
      rw [hleftFin, hrightFin]
      rw [hv.edge_left_label edge hedgeMem]
      rw [hv.edge_right_label edge hedgeMem]
      exact edge.compatible
  · rcases hrightSide with hrightL | hrightR
    · have hleftFin :
          left = ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hleftR
      have hrightFin :
          right = ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩ := by
        apply Fin.ext
        exact hrightL
      rw [hleftFin, hrightFin]
      rw [hv.edge_right_label edge hedgeMem]
      rw [hv.edge_left_label edge hedgeMem]
      exact Sig.compatible_symm edge.compatible
    · have hfin : left = right := by
        apply Fin.ext
        exact hleftR.trans hrightR.symm
      exact False.elim (hne hfin)

theorem edgeTwoEndpointsOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (edgeIndex : Fin st.edges.length) :
    ∃ left right : Fin st.endpoints.length,
      left ≠ right ∧
      endpointEdgeOfPartition hp left = edgeIndex ∧
      endpointEdgeOfPartition hp right = edgeIndex ∧
      ∀ endpoint : Fin st.endpoints.length,
        endpointEdgeOfPartition hp endpoint = edgeIndex →
          endpoint = left ∨ endpoint = right := by
  let edge := st.edges.get edgeIndex
  have hedgeMem : edge ∈ st.edges := List.get_mem st.edges edgeIndex
  let leftEndpoint : Fin st.endpoints.length :=
    ⟨edge.left, hv.edge_left_bound edge hedgeMem⟩
  let rightEndpoint : Fin st.endpoints.length :=
    ⟨edge.right, hv.edge_right_bound edge hedgeMem⟩
  refine ⟨leftEndpoint, rightEndpoint, ?_, ?_, ?_, ?_⟩
  · intro hsame
    have hval : edge.left = edge.right := by
      exact congrArg Fin.val hsame
    exact edge_left_ne_right_of_partition hp edgeIndex hval
  · exact endpointEdgeOfPartition_left hv hp edgeIndex
  · exact endpointEdgeOfPartition_right hv hp edgeIndex
  · intro endpoint hendpointEdge
    have hsideRaw := endpointEdgeOfPartition_endpoint hp endpoint
    have hside : endpoint.val = edge.left ∨ endpoint.val = edge.right := by
      simpa [edge, hendpointEdge] using hsideRaw
    rcases hside with hleft | hright
    · left
      apply Fin.ext
      exact hleft
    · right
      apply Fin.ext
      exact hright

/--
The semantic endpoint-to-edge slice of graph evidence derived from renderer
invariants.  Full `PortHypergraphEvidence` additionally needs edge
compatibility, two-endpoint edge laws, boundary ports, constructor incidence,
and owner uniqueness.
-/
structure EndpointEdgeEvidence {Sig : Signature}
    (st : RenderState Sig []) where
  endpointEdge : Fin st.endpoints.length → Fin st.edges.length
  endpoint_edge_label :
    ∀ endpoint : Fin st.endpoints.length,
      Sig.portEdge (st.endpoints.get endpoint) =
        (st.edges.get (endpointEdge endpoint)).label

def endpointEdgeEvidenceOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    EndpointEdgeEvidence st where
  endpointEdge := endpointEdgeOfPartition hp
  endpoint_edge_label := endpointEdgeOfPartition_label hv hp

/--
Renderer-derived semantic edge evidence.  This packages the endpoint-to-edge
assignment together with the compatibility and two-endpoint laws required by
`PortHypergraph`.
-/
structure EdgeEvidence {Sig : Signature}
    (st : RenderState Sig []) where
  endpointEdgeEvidence : EndpointEdgeEvidence st
  edge_compatible :
    ∀ left right : Fin st.endpoints.length,
      endpointEdgeEvidence.endpointEdge left =
        endpointEdgeEvidence.endpointEdge right →
      left ≠ right →
        Sig.compatible (st.endpoints.get left) (st.endpoints.get right)
  edge_two_endpoints :
    ∀ edge : Fin st.edges.length,
      ∃ left right : Fin st.endpoints.length,
        left ≠ right ∧
        endpointEdgeEvidence.endpointEdge left = edge ∧
        endpointEdgeEvidence.endpointEdge right = edge ∧
        ∀ endpoint : Fin st.endpoints.length,
          endpointEdgeEvidence.endpointEdge endpoint = edge →
            endpoint = left ∨ endpoint = right

def edgeEvidenceOfPartition
    {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    EdgeEvidence st where
  endpointEdgeEvidence := endpointEdgeEvidenceOfPartition hv hp
  edge_compatible := by
    intro left right hsame hne
    exact edgeCompatibleOfPartition hv hp left right hsame hne
  edge_two_endpoints := by
    intro edge
    exact edgeTwoEndpointsOfPartition hv hp edge

def incidentOfValidIds {Sig : Signature} {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length) :
    List (Fin st.endpoints.length) :=
  List.ofFn fun slot : Fin ((st.nodes.get node).incident.length) =>
    ⟨(st.nodes.get node).incident.get slot,
      hv.node_incident_bound (st.nodes.get node)
        (List.get_mem st.nodes node) slot⟩

theorem incidentOfValidIds_val_mem_nodeIncidentIds {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length)
    (slot : Fin (incidentOfValidIds hv node).length) :
    ((incidentOfValidIds hv node).get slot).val ∈ st.nodeIncidentIds := by
  simp [incidentOfValidIds, nodeIncidentIds]
  refine ⟨st.nodes.get node, List.get_mem st.nodes node, ?_⟩
  exact List.get_mem (st.nodes.get node).incident
    (Fin.cast (by simp [incidentOfValidIds]) slot)

theorem incidentOfValidIds_exists_of_mem_nodeIncidentIds {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (endpoint : Fin st.endpoints.length)
    (hnode : endpoint.val ∈ st.nodeIncidentIds) :
    ∃ (node : Fin st.nodes.length)
      (slot : Fin (incidentOfValidIds hv node).length),
      (incidentOfValidIds hv node).get slot = endpoint := by
  have hnodeMem := hnode
  simp [nodeIncidentIds] at hnodeMem
  rcases hnodeMem with ⟨renderNode, hrenderNode, hincidentMem⟩
  rcases list_exists_get_of_mem st.nodes hrenderNode with
    ⟨node, hnodeEq⟩
  have hincidentMem' :
      endpoint.val ∈ (st.nodes.get node).incident := by
    rw [hnodeEq]
    exact hincidentMem
  rcases list_exists_get_of_mem (st.nodes.get node).incident
      hincidentMem' with
    ⟨rawSlot, hrawSlot⟩
  let slot : Fin (incidentOfValidIds hv node).length :=
    Fin.cast (by simp [incidentOfValidIds]) rawSlot
  refine ⟨node, slot, ?_⟩
  apply Fin.ext
  simpa [incidentOfValidIds, slot] using hrawSlot

theorem incidentOfValidIds_length {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length) :
    (incidentOfValidIds hv node).length =
      Sig.arity ((st.nodes.get node).label) :=
  by
    simpa [incidentOfValidIds] using
      hv.node_incident_length (st.nodes.get node) (List.get_mem st.nodes node)

theorem incidentOfValidIds_injective {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (hn : st.NodeIncidentNodup)
    (node : Fin st.nodes.length) :
    Function.Injective fun slot : Fin (incidentOfValidIds hv node).length =>
      (incidentOfValidIds hv node).get slot := by
  intro i j h
  have hi :
      (st.nodes.get node).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) i) =
        (st.nodes.get node).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) j) := by
    have hval := congrArg Fin.val h
    simpa [incidentOfValidIds] using hval
  have horig :=
    list_get_injective_of_nodup (st.nodes.get node).incident
      (hn.node_incident_nodup (st.nodes.get node)
        (List.get_mem st.nodes node)) hi
  apply Fin.ext
  have hval := congrArg Fin.val horig
  simpa using hval

theorem incidentOfValidIds_label {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (node : Fin st.nodes.length)
    (slot : Fin (incidentOfValidIds hv node).length) :
    st.endpoints.get ((incidentOfValidIds hv node).get slot) =
      Sig.port ((st.nodes.get node).label)
        (Fin.cast (incidentOfValidIds_length hv node) slot) := by
  have hlabel :=
    hv.node_incident_label (st.nodes.get node)
      (List.get_mem st.nodes node)
      (Fin.cast (by simp [incidentOfValidIds]) slot)
  simpa [incidentOfValidIds, incidentOfValidIds_length] using hlabel

theorem boundaryEvidenceOfPrefix_ne_incidentOfValidIds {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (pref : EndpointPrefix st boundary)
    (hv : st.ValidIds)
    (ho : st.OwnerIdPartition boundary)
    (b : Fin boundary.length) (node : Fin st.nodes.length)
    (slot : Fin (incidentOfValidIds hv node).length) :
    (boundaryEvidenceOfPrefix pref).boundaryPort b ≠
      (incidentOfValidIds hv node).get slot := by
  intro h
  have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) h
  have hboundary : b.val ∈ List.range boundary.length :=
    List.mem_range.mpr b.isLt
  have hnodeRaw :
      ((incidentOfValidIds hv node).get slot).val ∈ st.nodeIncidentIds :=
    incidentOfValidIds_val_mem_nodeIncidentIds hv node slot
  have hnode : b.val ∈ st.nodeIncidentIds := by
    have hval' :
        ((boundaryEvidenceOfPrefix pref).boundaryPort b).val =
          ((incidentOfValidIds hv node).get slot).val := by
      simpa using hval
    have hincident :
        ((incidentOfValidIds hv node).get slot).val = b.val := by
      exact hval'.symm.trans
        (boundaryEvidenceOfPrefix_boundaryPort_val pref b)
    exact hincident ▸ hnodeRaw
  exact ho.boundary_nodeIncidentIds_disjoint hboundary hnode

theorem nodeIncidentIds_get_node_eq_of_nodup {Sig : Signature} :
    ∀ (nodes : List (RenderNode Sig)),
      (nodes.flatMap fun node => node.incident).Nodup →
      ∀ {leftNode rightNode : Fin nodes.length}
        {leftSlot : Fin ((nodes.get leftNode).incident.length)}
        {rightSlot : Fin ((nodes.get rightNode).incident.length)},
        (nodes.get leftNode).incident.get leftSlot =
          (nodes.get rightNode).incident.get rightSlot →
        leftNode = rightNode
  | [], _hnodup, leftNode, _rightNode, _leftSlot, _rightSlot, _h => by
      cases leftNode with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | head :: tail, hnodup, leftNode, rightNode, leftSlot, rightSlot, h => by
      have hflat :
          (head.incident ++ tail.flatMap fun node => node.incident).Nodup := by
        simpa using hnodup
      cases leftNode with
      | mk leftVal leftLt =>
          cases rightNode with
          | mk rightVal rightLt =>
              cases leftVal with
              | zero =>
                  cases rightVal with
                  | zero => rfl
                  | succ rightTailVal =>
                      let rightTail : Fin tail.length :=
                        ⟨rightTailVal, Nat.lt_of_succ_lt_succ rightLt⟩
                      let rightSlotTail :
                          Fin ((tail.get rightTail).incident.length) :=
                        Fin.cast (by simp [rightTail]) rightSlot
                      have hleftMem :
                          head.incident.get leftSlot ∈ head.incident :=
                        List.get_mem head.incident leftSlot
                      have hrightMemRaw :
                          (tail.get rightTail).incident.get rightSlotTail ∈
                            tail.flatMap fun node => node.incident := by
                        simp
                        exact ⟨tail.get rightTail, List.get_mem tail rightTail,
                          List.get_mem (tail.get rightTail).incident rightSlotTail⟩
                      have heq :
                          head.incident.get leftSlot =
                            (tail.get rightTail).incident.get rightSlotTail := by
                        simpa [rightTail, rightSlotTail] using h
                      have hrightMem :
                          head.incident.get leftSlot ∈
                            tail.flatMap fun node => node.incident := by
                        rw [← heq] at hrightMemRaw
                        exact hrightMemRaw
                      exact False.elim
                        (nodup_append_disjoint head.incident
                          (tail.flatMap fun node => node.incident)
                          hflat hleftMem hrightMem)
              | succ leftTailVal =>
                  cases rightVal with
                  | zero =>
                      let leftTail : Fin tail.length :=
                        ⟨leftTailVal, Nat.lt_of_succ_lt_succ leftLt⟩
                      let leftSlotTail :
                          Fin ((tail.get leftTail).incident.length) :=
                        Fin.cast (by simp [leftTail]) leftSlot
                      have hleftMemRaw :
                          (tail.get leftTail).incident.get leftSlotTail ∈
                            tail.flatMap fun node => node.incident := by
                        simp
                        exact ⟨tail.get leftTail, List.get_mem tail leftTail,
                          List.get_mem (tail.get leftTail).incident leftSlotTail⟩
                      have heq :
                          (tail.get leftTail).incident.get leftSlotTail =
                            head.incident.get rightSlot := by
                        simpa [leftTail, leftSlotTail] using h
                      have hleftMem :
                          head.incident.get rightSlot ∈
                            tail.flatMap fun node => node.incident := by
                        rw [heq] at hleftMemRaw
                        exact hleftMemRaw
                      have hrightMem :
                          head.incident.get rightSlot ∈ head.incident :=
                        List.get_mem head.incident rightSlot
                      exact False.elim
                        (nodup_append_disjoint head.incident
                          (tail.flatMap fun node => node.incident)
                          hflat hrightMem hleftMem)
                  | succ rightTailVal =>
                      let leftTail : Fin tail.length :=
                        ⟨leftTailVal, Nat.lt_of_succ_lt_succ leftLt⟩
                      let rightTail : Fin tail.length :=
                        ⟨rightTailVal, Nat.lt_of_succ_lt_succ rightLt⟩
                      let leftSlotTail :
                          Fin ((tail.get leftTail).incident.length) :=
                        Fin.cast (by simp [leftTail]) leftSlot
                      let rightSlotTail :
                          Fin ((tail.get rightTail).incident.length) :=
                        Fin.cast (by simp [rightTail]) rightSlot
                      have htail :
                          (tail.get leftTail).incident.get leftSlotTail =
                            (tail.get rightTail).incident.get rightSlotTail := by
                        simpa [leftTail, rightTail, leftSlotTail, rightSlotTail]
                          using h
                      have htailNodup :
                          (tail.flatMap fun node => node.incident).Nodup :=
                        nodup_append_right head.incident
                          (tail.flatMap fun node => node.incident) hflat
                      have hnodeTail :
                          leftTail = rightTail :=
                        nodeIncidentIds_get_node_eq_of_nodup tail htailNodup
                          htail
                      apply Fin.ext
                      have hval := congrArg (fun idx : Fin tail.length => idx.val)
                        hnodeTail
                      exact congrArg Nat.succ hval

theorem incidentOfValidIds_eq_node_eq {Sig : Signature}
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (ho : st.OwnerIdPartition boundary)
    {leftNode rightNode : Fin st.nodes.length}
    {leftSlot : Fin (incidentOfValidIds hv leftNode).length}
    {rightSlot : Fin (incidentOfValidIds hv rightNode).length}
    (h :
      (incidentOfValidIds hv leftNode).get leftSlot =
        (incidentOfValidIds hv rightNode).get rightSlot) :
    leftNode = rightNode := by
  have hraw :
      (st.nodes.get leftNode).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) leftSlot) =
        (st.nodes.get rightNode).incident.get
          (Fin.cast (by simp [incidentOfValidIds]) rightSlot) := by
    have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) h
    simpa [incidentOfValidIds] using hval
  exact nodeIncidentIds_get_node_eq_of_nodup st.nodes
    (by simpa [nodeIncidentIds] using ho.nodeIncidentIds_nodup) hraw

/--
Renderer-derived constructor incidence evidence.  It turns each rendered node's
ordered incident endpoint IDs into finite endpoint references and proves the
length, injectivity, and label laws required by `PortHypergraph`.
-/
structure IncidenceEvidence {Sig : Signature}
    (st : RenderState Sig []) where
  incident : Fin st.nodes.length → List (Fin st.endpoints.length)
  incident_length :
    ∀ node : Fin st.nodes.length,
      (incident node).length = Sig.arity ((st.nodes.get node).label)
  incident_injective :
    ∀ node : Fin st.nodes.length,
      Function.Injective fun slot : Fin (incident node).length =>
        (incident node).get slot
  incidence_label :
    ∀ (node : Fin st.nodes.length) (slot : Fin (incident node).length),
      st.endpoints.get ((incident node).get slot) =
        Sig.port ((st.nodes.get node).label) (Fin.cast (incident_length node) slot)

def incidenceEvidenceOfValidIds {Sig : Signature}
    {st : RenderState Sig []}
    (hv : st.ValidIds) (hn : st.NodeIncidentNodup) :
    IncidenceEvidence st where
  incident := incidentOfValidIds hv
  incident_length := incidentOfValidIds_length hv
  incident_injective := incidentOfValidIds_injective hv hn
  incidence_label := incidentOfValidIds_label hv

theorem ValidIds.frontier_head_label {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {st : RenderState Sig (active :: frontier)}
    (hv : st.ValidIds)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    st.endpoints.get
      ⟨activeId, hv.frontier_bound activeId (by rw [hids]; simp)⟩ =
      active := by
  have hlabel :=
    hv.frontier_label 0 (by rw [hids]; simp) (by simp)
  simpa [hids] using hlabel

theorem ValidIds.frontier_tail_label {Sig : Signature}
    {active : Sig.Port} {frontier : List Sig.Port}
    {st : RenderState Sig (active :: frontier)}
    (hv : st.ValidIds)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    (hrest : restIds.length = frontier.length)
    (i : Fin restIds.length) :
    st.endpoints.get
      ⟨restIds.get i,
        hv.frontier_bound (restIds.get i) (by rw [hids]; simp)⟩ =
      frontier.get (Fin.cast hrest i) := by
  have hlabel :=
    hv.frontier_label (i.val + 1)
      (by rw [hids]; simp [i.isLt])
      (by
        have hi : i.val < frontier.length := by
          simp [← hrest, i.isLt]
        simpa using Nat.succ_lt_succ hi)
  simpa [hids] using hlabel

/--
Raw endpoint-ID reachability for intermediate renderer states.  This relation
is defined before the semantic `PortHypergraph` exists, so it can be preserved
through render steps that still have pending frontier endpoints.
-/
inductive RawReachesBoundary {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundaryLength : Nat) :
    Nat → Prop
  | boundary {id : Nat} (hboundary : id ∈ List.range boundaryLength) :
      RawReachesBoundary st boundaryLength id
  | throughEdgeLeft (edge : RenderEdge Sig) (hmem : edge ∈ st.edges)
      (reach : RawReachesBoundary st boundaryLength edge.left) :
      RawReachesBoundary st boundaryLength edge.right
  | throughEdgeRight (edge : RenderEdge Sig) (hmem : edge ∈ st.edges)
      (reach : RawReachesBoundary st boundaryLength edge.right) :
      RawReachesBoundary st boundaryLength edge.left
  | throughConstructor (node : RenderNode Sig) (hmem : node ∈ st.nodes)
      (fromSlot toSlot : Fin node.incident.length)
      (reach :
        RawReachesBoundary st boundaryLength
          (node.incident.get fromSlot)) :
      RawReachesBoundary st boundaryLength (node.incident.get toSlot)

theorem RawReachesBoundary.mono
    {Sig : Signature} {frontier frontier' : List Sig.Port}
    {st : RenderState Sig frontier} {st' : RenderState Sig frontier'}
    {boundaryLength id : Nat}
    (hedges : ∀ edge : RenderEdge Sig, edge ∈ st.edges → edge ∈ st'.edges)
    (hnodes : ∀ node : RenderNode Sig, node ∈ st.nodes → node ∈ st'.nodes)
    (reach : st.RawReachesBoundary boundaryLength id) :
    st'.RawReachesBoundary boundaryLength id := by
  induction reach with
  | boundary hboundary =>
      exact RawReachesBoundary.boundary hboundary
  | throughEdgeLeft edge hmem _reach ih =>
      exact RawReachesBoundary.throughEdgeLeft edge (hedges edge hmem) ih
  | throughEdgeRight edge hmem _reach ih =>
      exact RawReachesBoundary.throughEdgeRight edge (hedges edge hmem) ih
  | throughConstructor node hmem fromSlot toSlot _reach ih =>
      exact RawReachesBoundary.throughConstructor node (hnodes node hmem)
        fromSlot toSlot ih

/--
Reachability invariant for intermediate renderer states.  Every pending
endpoint is already in the boundary-connected component, and every rendered
constructor has at least one incident endpoint in that component.
-/
structure Reachability {Sig : Signature} {frontier : List Sig.Port}
    (st : RenderState Sig frontier) (boundary : List Sig.Port) : Prop where
  frontier_reaches :
    ∀ id : Nat, id ∈ st.frontierIds →
      st.RawReachesBoundary boundary.length id
  node_reaches :
    ∀ node : RenderNode Sig, node ∈ st.nodes →
      ∃ slot : Fin node.incident.length,
        st.RawReachesBoundary boundary.length (node.incident.get slot)

theorem initial_reachability {Sig : Signature} (boundary : List Sig.Port) :
    (initial Sig boundary).Reachability boundary where
  frontier_reaches := by
    intro id hid
    exact RawReachesBoundary.boundary (by
      simpa [initial] using hid)
  node_reaches := by
    intro node hmem
    simp [initial] at hmem

end RenderState

namespace Diag

variable {Sig : Signature}

def freshNodeEndpoints (start arity : Nat) : List Nat :=
  (List.range arity).map fun offset => start + offset

@[simp]
theorem freshNodeEndpoints_length (start arity : Nat) :
    (freshNodeEndpoints start arity).length = arity := by
  simp [freshNodeEndpoints]

theorem freshNodeEndpoints_get (start arity : Nat)
    (i : Fin (freshNodeEndpoints start arity).length) :
    (freshNodeEndpoints start arity).get i = start + i.val := by
  simp [freshNodeEndpoints]

theorem freshNodeEndpoints_mem_lt {start arity id : Nat}
    (hmem : id ∈ freshNodeEndpoints start arity) :
    id < start + arity := by
  rcases list_exists_get_of_mem (freshNodeEndpoints start arity) hmem with
    ⟨i, hi⟩
  rw [← hi, freshNodeEndpoints_get]
  have hiLt : i.val < arity := by
    simpa using i.isLt
  omega

theorem freshNodeEndpoints_mem_ge {start arity id : Nat}
    (hmem : id ∈ freshNodeEndpoints start arity) :
    start ≤ id := by
  rcases list_exists_get_of_mem (freshNodeEndpoints start arity) hmem with
    ⟨i, hi⟩
  rw [← hi, freshNodeEndpoints_get]
  exact Nat.le_add_right start i.val

theorem freshNodeEndpoints_mem_of_bounds {start arity id : Nat}
    (hge : start ≤ id) (hlt : id < start + arity) :
    id ∈ freshNodeEndpoints start arity := by
  simp [freshNodeEndpoints]
  refine ⟨id - start, ?_, ?_⟩
  · omega
  · omega

theorem freshNodeEndpoints_nodup (start arity : Nat) :
    (freshNodeEndpoints start arity).Nodup := by
  apply list_nodup_of_get_injective
  intro i j hget
  change (freshNodeEndpoints start arity).get i =
    (freshNodeEndpoints start arity).get j at hget
  rw [freshNodeEndpoints_get, freshNodeEndpoints_get] at hget
  apply Fin.ext
  omega

theorem freshNodeEndpoints_label_append
    {frontier : List Sig.Port} (st : RenderState Sig frontier)
    (hv : st.ValidIds) (node : Sig.Node)
    (i : Fin (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).length)
    (hbound :
      (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i <
        (st.endpoints ++ Sig.nodePorts node).length) :
    (st.endpoints ++ Sig.nodePorts node).get
        ⟨(freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i,
          hbound⟩ =
      (Sig.nodePorts node).get
        (Fin.cast (by simp [freshNodeEndpoints, Signature.nodePorts]) i) := by
  have hget :=
    freshNodeEndpoints_get st.nextEndpoint (Sig.arity node) i
  have hbound' :
      st.nextEndpoint + i.val <
        (st.endpoints ++ Sig.nodePorts node).length := by
    simpa [← hget] using hbound
  have hright :
      st.endpoints.length ≤ st.nextEndpoint + i.val := by
    have hnext := hv.nextEndpoint_eq
    omega
  calc
    (st.endpoints ++ Sig.nodePorts node).get
        ⟨(freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get i,
          hbound⟩ =
        (st.endpoints ++ Sig.nodePorts node).get
          ⟨st.nextEndpoint + i.val, hbound'⟩ := by
          apply congrArg (fun idx =>
            (st.endpoints ++ Sig.nodePorts node).get idx)
          apply Fin.ext
          exact hget
    _ =
        (Sig.nodePorts node).get
          ⟨st.nextEndpoint + i.val - st.endpoints.length, by
            have hlen :
                (st.endpoints ++ Sig.nodePorts node).length =
                  st.endpoints.length + (Sig.nodePorts node).length := by
              simp
            omega⟩ := by
          exact list_get_append_right st.endpoints (Sig.nodePorts node)
            hright hbound'
    _ =
        (Sig.nodePorts node).get
          (Fin.cast (by simp [freshNodeEndpoints, Signature.nodePorts]) i) := by
          have hsub :
              st.nextEndpoint + i.val - st.endpoints.length = i.val := by
            have hnext := hv.nextEndpoint_eq
            omega
          apply congrArg (fun idx => (Sig.nodePorts node).get idx)
          apply Fin.ext
          simp [hsub]

/--
One `connect` rendering step.  The type records the frontier effect: the
active endpoint and selected mate are consumed, leaving `eraseFin frontier
mate`.
-/
def connectStep {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    RenderState Sig (eraseFin frontier mate) :=
  match hids : st.frontierIds with
  | [] =>
      False.elim (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simp at hlen)
  | activeId :: restIds =>
      have hrest : restIds.length = frontier.length := by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simpa using Nat.succ.inj hlen
      let mateId := restIds.get (Fin.cast hrest.symm mate)
      let childIds := eraseFin restIds (Fin.cast hrest.symm mate)
      { nextEndpoint := st.nextEndpoint
        endpoints := st.endpoints
        edges := st.edges ++
          [{ label := Sig.portEdge active
             leftLabel := active
             rightLabel := frontier.get mate
             left := activeId
             right := mateId
             left_label := rfl
             right_label := (Sig.compatible_edge ok).symm
             compatible := ok }]
        nodes := st.nodes
        frontierIds := childIds
        frontierIds_length := by
          dsimp [childIds]
          simp [eraseFin_length, hrest] }

/--
One `bud` rendering step.  The type records the frontier effect: the active
endpoint and selected constructor entry are consumed, and the remaining ordered
constructor endpoints are appended after the existing rest frontier.
-/
def budStep {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    RenderState Sig (frontier ++ Sig.nodePortsExcept node entry) :=
  match hids : st.frontierIds with
  | [] =>
      False.elim (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simp at hlen)
  | activeId :: restIds =>
      have hrest : restIds.length = frontier.length := by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        simpa using Nat.succ.inj hlen
      let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
      let entryId := nodeEndpoints.get
        (Fin.cast (by simp [nodeEndpoints]) entry)
      let childIds := restIds ++
        eraseFin nodeEndpoints (Fin.cast (by simp [nodeEndpoints]) entry)
      { nextEndpoint := st.nextEndpoint + Sig.arity node
        endpoints := st.endpoints ++ Sig.nodePorts node
        edges := st.edges ++
          [{ label := Sig.portEdge active
             leftLabel := active
             rightLabel := Sig.port node entry
             left := activeId
             right := entryId
             left_label := rfl
             right_label := (Sig.compatible_edge ok).symm
             compatible := ok }]
        nodes := st.nodes ++ [{ label := node, incident := nodeEndpoints }]
        frontierIds := childIds
        frontierIds_length := by
          dsimp [childIds]
          simp [hrest, Signature.nodePortsExcept, Signature.nodePorts,
            nodeEndpoints, eraseFin_length] }

theorem connectStep_edge_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {edge : RenderEdge Sig}
    (hmem : edge ∈ st.edges) :
    edge ∈ (connectStep mate ok st).edges := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [hmem]

theorem connectStep_node_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {node : RenderNode Sig}
    (hmem : node ∈ st.nodes) :
    node ∈ (connectStep mate ok st).nodes := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simpa using hmem

theorem connectStep_node_mem_old_of_child
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {node : RenderNode Sig}
    (hmem : node ∈ (connectStep mate ok st).nodes) :
    node ∈ st.nodes := by
  unfold connectStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simpa using hmem

/-- The concrete edge introduced by a `connect` render step is present in the
step result. -/
theorem connectStep_new_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := frontier.get mate
       left := activeId
       right :=
        restIds.get (Fin.cast (by
          have hlen := st.frontierIds_length
          rw [hids] at hlen
          exact (Nat.succ.inj hlen).symm) mate)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (connectStep mate ok st).edges := by
  unfold connectStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    simp

theorem connectStep_frontier_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {id : Nat}
    (hmem : id ∈ (connectStep mate ok st).frontierIds) :
    id ∈ st.frontierIds := by
  unfold connectStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    rw [hids]
    right
    exact mem_of_mem_eraseFin restIds (Fin.cast hrest.symm mate) hmem

theorem connectStep_rawReachesBoundary_of_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port} {id : Nat}
    (reach : st.RawReachesBoundary boundary.length id) :
    (connectStep mate ok st).RawReachesBoundary boundary.length id :=
  RenderState.RawReachesBoundary.mono
    (st := st)
    (st' := connectStep mate ok st)
    (boundaryLength := boundary.length)
    (id := id)
    (fun _edge hmem => connectStep_edge_mem_old mate ok st hmem)
    (fun _node hmem => connectStep_node_mem_old mate ok st hmem)
    reach

theorem connectStep_reachability {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary) :
    (connectStep mate ok st).Reachability boundary where
  frontier_reaches := by
    intro id hmem
    exact connectStep_rawReachesBoundary_of_old mate ok st
      (hr.frontier_reaches id
        (connectStep_frontier_mem_old mate ok st hmem))
  node_reaches := by
    intro node hmem
    rcases hr.node_reaches node
        (connectStep_node_mem_old_of_child mate ok st hmem) with
      ⟨slot, reach⟩
    exact ⟨slot, connectStep_rawReachesBoundary_of_old mate ok st reach⟩

theorem budStep_edge_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {edge : RenderEdge Sig}
    (hmem : edge ∈ st.edges) :
    edge ∈ (budStep node entry ok st).edges := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [hmem]

theorem budStep_node_mem_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {renderNode : RenderNode Sig}
    (hmem : renderNode ∈ st.nodes) :
    renderNode ∈ (budStep node entry ok st).nodes := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [hmem]

theorem budStep_rawReachesBoundary_of_old
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port} {id : Nat}
    (reach : st.RawReachesBoundary boundary.length id) :
    (budStep node entry ok st).RawReachesBoundary boundary.length id :=
  RenderState.RawReachesBoundary.mono
    (st := st)
    (st' := budStep node entry ok st)
    (boundaryLength := boundary.length)
    (id := id)
    (fun _edge hmem => budStep_edge_mem_old node entry ok st hmem)
    (fun _node hmem => budStep_node_mem_old node entry ok st hmem)
    reach

theorem budStep_node_mem_old_or_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {renderNode : RenderNode Sig}
    (hmem : renderNode ∈ (budStep node entry ok st).nodes) :
    renderNode ∈ st.nodes ∨
      renderNode =
        { label := node
          incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) } := by
  unfold budStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [freshNodeEndpoints] at hmem
    exact hmem

theorem budStep_frontier_mem_old_or_new
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {id : Nat}
    (hmem : id ∈ (budStep node entry ok st).frontierIds) :
    id ∈ st.frontierIds ∨
      id ∈
        eraseFin (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
          (Fin.cast (by simp [freshNodeEndpoints]) entry) := by
  unfold budStep at hmem
  split at hmem
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    simp [freshNodeEndpoints] at hmem
    rcases hmem with hold | hnew
    · left
      rw [hids]
      simp [hold]
    · right
      simpa [freshNodeEndpoints] using hnew

theorem budStep_new_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := Sig.port node entry
       left := activeId
       right :=
        (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
          (Fin.cast (by simp [freshNodeEndpoints]) entry)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (budStep node entry ok st).edges := by
  unfold budStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · rename_i activeId' restIds' hids'
    rw [hids] at hids'
    injection hids' with hactive hrest
    subst activeId'
    subst restIds'
    simp [freshNodeEndpoints]

theorem budStep_new_node_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    ({ label := node
       incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) } :
        RenderNode Sig) ∈
      (budStep node entry ok st).nodes := by
  unfold budStep
  split
  · rename_i hidsNil
    exact False.elim (RenderState.frontierIds_ne_nil st hidsNil)
  · simp [freshNodeEndpoints]

theorem budStep_entry_rawReachesBoundary
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    (budStep node entry ok st).RawReachesBoundary boundary.length
      ((freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
        (Fin.cast (by simp [freshNodeEndpoints]) entry)) := by
  let entryIdx : Fin (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).length :=
    Fin.cast (by simp [freshNodeEndpoints]) entry
  let entryId := (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get entryIdx
  let newEdge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := activeId
      right := entryId
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hactiveReach :
      st.RawReachesBoundary boundary.length activeId :=
    hr.frontier_reaches activeId (by
      rw [hids]
      simp)
  have hactiveReachChild :
      (budStep node entry ok st).RawReachesBoundary boundary.length activeId :=
    budStep_rawReachesBoundary_of_old node entry ok st hactiveReach
  change
    (budStep node entry ok st).RawReachesBoundary boundary.length entryId
  exact RenderState.RawReachesBoundary.throughEdgeLeft newEdge
    (by
      dsimp [newEdge, entryId, entryIdx]
      exact budStep_new_edge_mem node entry ok st hids)
    hactiveReachChild

theorem budStep_fresh_rawReachesBoundary
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds)
    {id : Nat}
    (hfresh :
      id ∈ freshNodeEndpoints st.nextEndpoint (Sig.arity node)) :
    (budStep node entry ok st).RawReachesBoundary boundary.length id := by
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    Fin.cast (by simp [nodeEndpoints, freshNodeEndpoints]) entry
  rcases list_exists_get_of_mem nodeEndpoints hfresh with ⟨toSlot, hto⟩
  let newNode : RenderNode Sig := { label := node, incident := nodeEndpoints }
  have hentryReach :
      (budStep node entry ok st).RawReachesBoundary boundary.length
        (nodeEndpoints.get entryIdx) := by
    dsimp [nodeEndpoints, entryIdx]
    exact budStep_entry_rawReachesBoundary node entry ok st hr hids
  have htoReach :
      (budStep node entry ok st).RawReachesBoundary boundary.length
        (newNode.incident.get toSlot) :=
    RenderState.RawReachesBoundary.throughConstructor newNode
      (by
        dsimp [newNode, nodeEndpoints]
        exact budStep_new_node_mem node entry ok st)
      entryIdx toSlot hentryReach
  exact hto ▸ htoReach

theorem budStep_reachability {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hr : st.Reachability boundary) :
    (budStep node entry ok st).Reachability boundary := by
  cases hids : st.frontierIds with
  | nil =>
      exact False.elim (RenderState.frontierIds_ne_nil st hids)
  | cons activeId restIds =>
      refine
        { frontier_reaches := ?_
          node_reaches := ?_ }
      · intro id hmem
        rcases budStep_frontier_mem_old_or_new node entry ok st hmem with
          hold | hnew
        · exact budStep_rawReachesBoundary_of_old node entry ok st
            (hr.frontier_reaches id hold)
        · exact budStep_fresh_rawReachesBoundary node entry ok st hr hids
            (mem_of_mem_eraseFin
              (freshNodeEndpoints st.nextEndpoint (Sig.arity node))
              (Fin.cast (by simp [freshNodeEndpoints]) entry)
              hnew)
      · intro renderNode hmem
        rcases budStep_node_mem_old_or_new node entry ok st hmem with
          hold | hnew
        · rcases hr.node_reaches renderNode hold with ⟨slot, reach⟩
          exact ⟨slot, budStep_rawReachesBoundary_of_old node entry ok st reach⟩
        · subst renderNode
          let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
          let entryIdx : Fin nodeEndpoints.length :=
            Fin.cast (by simp [nodeEndpoints, freshNodeEndpoints]) entry
          refine ⟨entryIdx, ?_⟩
          dsimp [nodeEndpoints, entryIdx]
          exact budStep_entry_rawReachesBoundary node entry ok st hr hids

theorem connectStep_validIds {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) :
    (connectStep mate ok st).ValidIds := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    dsimp
    refine
      { nextEndpoint_eq := hv.nextEndpoint_eq
        frontier_bound := ?_
        frontier_label := ?_
        edge_left_bound := ?_
        edge_right_bound := ?_
        edge_left_label := ?_
        edge_right_label := ?_
        node_incident_length := hv.node_incident_length
        node_incident_bound := hv.node_incident_bound
        node_incident_label := hv.node_incident_label }
    · intro id hid
      exact hv.frontier_bound id (by
        rw [hids]
        right
        exact mem_of_mem_eraseFin restIds
          (Fin.cast hrest.symm mate) hid)
    · intro n hid hfrontier
      let idx : Fin restIds.length := Fin.cast hrest.symm mate
      have hrel :
          ∀ (n : Nat) (hx : n < restIds.length)
            (hy : n < frontier.length),
            ∃ hbound : restIds.get ⟨n, hx⟩ < st.endpoints.length,
              st.endpoints.get ⟨restIds.get ⟨n, hx⟩, hbound⟩ =
                frontier.get ⟨n, hy⟩ := by
        intro n hx hy
        have hlabel :=
          hv.frontier_tail_label hids hrest ⟨n, hx⟩
        refine ⟨hv.frontier_bound (restIds.get ⟨n, hx⟩) ?_, ?_⟩
        · rw [hids]
          right
          exact List.get_mem restIds ⟨n, hx⟩
        · simpa using hlabel
      have haligned :=
        eraseFin_pointwise_relation
          (R := fun id label =>
            ∃ hbound : id < st.endpoints.length,
              st.endpoints.get ⟨id, hbound⟩ = label)
          hrest hrel idx mate (by simp [idx]) n hid hfrontier
      rcases haligned with ⟨hbound, hlabel⟩
      simpa using hlabel
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_left_bound edge hold
      · cases hnew
        exact hv.frontier_bound activeId (by rw [hids]; simp)
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_right_bound edge hold
      · cases hnew
        exact hv.frontier_bound
          (restIds.get (Fin.cast hrest.symm mate)) (by
            rw [hids]
            right
            exact List.get_mem restIds (Fin.cast hrest.symm mate))
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_left_label edge hold
      · cases hnew
        exact hv.frontier_head_label hids
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.edge_right_label edge hold
      · cases hnew
        exact hv.frontier_tail_label hids hrest (Fin.cast hrest.symm mate)

theorem connectStep_endpointPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    (connectStep mate ok st).EndpointPartition := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    let idx : Fin restIds.length := Fin.cast hrest.symm mate
    have oldFrontierNodup : (activeId :: restIds).Nodup := by
      simpa [hids] using hp.frontier_nodup
    have active_not_rest : activeId ∉ restIds := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.1
    have rest_nodup : restIds.Nodup := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.2
    have active_ne_mate : activeId ≠ restIds.get idx := by
      intro hsame
      exact active_not_rest (by
        rw [hsame]
        exact List.get_mem restIds idx)
    have active_old_frontier : activeId ∈ st.frontierIds := by
      rw [hids]
      simp
    have mate_old_frontier : restIds.get idx ∈ st.frontierIds := by
      rw [hids]
      right
      exact List.get_mem restIds idx
    dsimp
    let newEdge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := frontier.get mate
        left := activeId
        right := restIds.get idx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    let child : RenderState Sig (eraseFin frontier mate) :=
      { nextEndpoint := st.nextEndpoint
        endpoints := st.endpoints
        edges := st.edges ++ [newEdge]
        nodes := st.nodes
        frontierIds := eraseFin restIds idx
        frontierIds_length := by
          dsimp [idx]
          simp [eraseFin_length, hrest] }
    change child.EndpointPartition
    have childConsumed_eq :
        child.edgeEndpointIds =
          st.edgeEndpointIds ++ [activeId, restIds.get idx] := by
      simp [child, newEdge, RenderState.edgeEndpointIds]
    refine
      { frontier_nodup := ?_
        consumed_nodup := ?_
        consumed_bound := ?_
        frontier_consumed_disjoint := ?_
        endpoint_covered := ?_ }
    · exact nodup_eraseFin restIds idx rest_nodup
    · have hnodup :
          (st.edgeEndpointIds ++ [activeId, restIds.get idx]).Nodup := by
        apply nodup_append_of_nodup_disjoint
        · exact hp.consumed_nodup
        · have hpair : ([activeId, restIds.get idx] : List Nat).Nodup := by
            simp
            exact active_ne_mate
          exact hpair
        · intro id hold hnew
          simp at hnew
          rcases hnew with hactive | hmate
          · exact hp.frontier_consumed_disjoint id
              (by simpa [hactive] using active_old_frontier) hold
          · exact hp.frontier_consumed_disjoint id
              (by simpa [hmate] using mate_old_frontier) hold
      rw [childConsumed_eq]
      exact hnodup
    · intro id hmem
      rw [childConsumed_eq] at hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hp.consumed_bound id hold
      · rcases hnew with hactive | hmate
        · have hbound := hv.frontier_bound activeId active_old_frontier
          simpa [hactive] using hbound
        · have hbound := hv.frontier_bound (restIds.get idx) mate_old_frontier
          simpa [hmate] using hbound
    · intro id hfrontier hconsumed
      rw [childConsumed_eq] at hconsumed
      simp at hconsumed
      rcases hconsumed with hold | hnew
      · have oldFrontier : id ∈ st.frontierIds := by
          rw [hids]
          right
          exact mem_of_mem_eraseFin restIds idx hfrontier
        exact hp.frontier_consumed_disjoint id oldFrontier hold
      · rcases hnew with hactive | hmate
        · have hrestMem : id ∈ restIds :=
            mem_of_mem_eraseFin restIds idx hfrontier
          exact active_not_rest (by simpa [hactive] using hrestMem)
        · have hnotMate :
            restIds.get idx ∉ eraseFin restIds idx :=
            get_not_mem_eraseFin_of_nodup restIds idx rest_nodup
          exact hnotMate (by simpa [hmate] using hfrontier)
    · intro id hid
      rcases hp.endpoint_covered id hid with holdFrontier | holdConsumed
      · rw [hids] at holdFrontier
        simp at holdFrontier
        rcases holdFrontier with hactive | hrestMem
        · right
          rw [childConsumed_eq]
          simp [hactive]
        · by_cases hmate : id = restIds.get idx
          · right
            rw [childConsumed_eq]
            simp [hmate]
          · left
            exact mem_eraseFin_of_mem_ne_get restIds idx hrestMem hmate
      · right
        rw [childConsumed_eq]
        simp [holdConsumed]

theorem connectStep_nodeIncidentNodup {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    (hn : st.NodeIncidentNodup) :
    (connectStep mate ok st).NodeIncidentNodup := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · constructor
    intro node hmem
    exact hn.node_incident_nodup node hmem

theorem connectStep_ownerIdPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (connectStep mate ok st).OwnerIdPartition boundary := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · constructor
    · simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
        using ho.owner_nodup
    · intro id hmem
      exact ho.owner_bound id (by
        simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
          using hmem)
    · intro id hid
      simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds] using
        ho.owner_covered id hid

theorem budStep_validIds {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) :
    (budStep node entry ok st).ValidIds := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    dsimp
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    have nodeEndpoints_length :
        nodeEndpoints.length = Sig.arity node := by
      simp [nodeEndpoints]
    have nodeEndpoints_labels :
        ∀ (n : Nat) (hid : n < nodeEndpoints.length)
          (hlabel : n < (Sig.nodePorts node).length),
          ∃ hbound : nodeEndpoints.get ⟨n, hid⟩ <
              (st.endpoints ++ Sig.nodePorts node).length,
            (st.endpoints ++ Sig.nodePorts node).get
                ⟨nodeEndpoints.get ⟨n, hid⟩, hbound⟩ =
              (Sig.nodePorts node).get ⟨n, hlabel⟩ := by
      intro n hid hlabel
      have hbound :
          nodeEndpoints.get ⟨n, hid⟩ <
            (st.endpoints ++ Sig.nodePorts node).length := by
        have hlt := freshNodeEndpoints_mem_lt
          (start := st.nextEndpoint) (arity := Sig.arity node)
          (id := nodeEndpoints.get ⟨n, hid⟩)
          (by
            simp [nodeEndpoints])
        have hnext := hv.nextEndpoint_eq
        simp [Signature.nodePorts] at hlt ⊢
        omega
      refine ⟨hbound, ?_⟩
      have hlabel' :=
        freshNodeEndpoints_label_append st hv node ⟨n, hid⟩ hbound
      simpa [nodeEndpoints] using hlabel'
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < (st.endpoints ++ Sig.nodePorts node).length := by
      have hle :
          st.endpoints.length ≤
            (st.endpoints ++ Sig.nodePorts node).length := by
        simp
      exact Nat.lt_of_lt_of_le hbound hle
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < (st.endpoints ++ Sig.nodePorts node).length := by
      have hlt := freshNodeEndpoints_mem_lt
        (by simpa [nodeEndpoints] using hmem)
      have hnext := hv.nextEndpoint_eq
      simp [Signature.nodePorts] at hlt ⊢
      omega
    refine
      { nextEndpoint_eq := ?_
        frontier_bound := ?_
        frontier_label := ?_
        edge_left_bound := ?_
        edge_right_bound := ?_
        edge_left_label := ?_
        edge_right_label := ?_
        node_incident_length := ?_
        node_incident_bound := ?_
        node_incident_label := ?_ }
    · simp [Signature.nodePorts, hv.nextEndpoint_eq]
    · intro id hid
      simp at hid
      rcases hid with hold | hnew
      · have holdBound := hv.frontier_bound id (by
          rw [hids]
          right
          exact hold)
        exact old_bound_lift holdBound
      · have hmem : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hnew
        exact fresh_bound_of_mem hmem
    · intro n hid hfrontier
      let portEntry : Fin (Sig.nodePorts node).length :=
        Fin.cast (by simp [Signature.nodePorts]) entry
      have hleft :
          ∀ (n : Nat) (hid : n < restIds.length)
            (hlabel : n < frontier.length),
            ∃ hbound : restIds.get ⟨n, hid⟩ <
                (st.endpoints ++ Sig.nodePorts node).length,
              (st.endpoints ++ Sig.nodePorts node).get
                  ⟨restIds.get ⟨n, hid⟩, hbound⟩ =
                frontier.get ⟨n, hlabel⟩ := by
        intro n hid hlabel
        have oldLabel :=
          hv.frontier_tail_label hids hrest ⟨n, hid⟩
        have oldBound :=
          hv.frontier_bound (restIds.get ⟨n, hid⟩) (by
            rw [hids]
            right
            exact List.get_mem restIds ⟨n, hid⟩)
        refine ⟨old_bound_lift oldBound, ?_⟩
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨restIds.get ⟨n, hid⟩, old_bound_lift oldBound⟩ =
              st.endpoints.get
                ⟨restIds.get ⟨n, hid⟩, oldBound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) oldBound (old_bound_lift oldBound)
          _ = frontier.get ⟨n, hlabel⟩ := by
              simpa using oldLabel
      have hright :
          ∀ (n : Nat)
            (hid : n < (eraseFin nodeEndpoints entryIdx).length)
            (hlabel : n < (Sig.nodePortsExcept node entry).length),
            ∃ hbound : (eraseFin nodeEndpoints entryIdx).get ⟨n, hid⟩ <
                (st.endpoints ++ Sig.nodePorts node).length,
              (st.endpoints ++ Sig.nodePorts node).get
                  ⟨(eraseFin nodeEndpoints entryIdx).get ⟨n, hid⟩,
                    hbound⟩ =
                (Sig.nodePortsExcept node entry).get ⟨n, hlabel⟩ := by
        intro n hid hlabel
        have hlabel' :
            n < (eraseFin (Sig.nodePorts node) portEntry).length := by
          simpa [Signature.nodePortsExcept, portEntry] using hlabel
        have haligned :=
          eraseFin_pointwise_relation
            (R := fun id label =>
              ∃ hbound : id <
                  (st.endpoints ++ Sig.nodePorts node).length,
                (st.endpoints ++ Sig.nodePorts node).get
                    ⟨id, hbound⟩ = label)
            (by simp [nodeEndpoints, Signature.nodePorts])
            nodeEndpoints_labels entryIdx portEntry
            (by simp [entryIdx, portEntry])
            n hid hlabel'
        rcases haligned with ⟨hbound, hlabelEq⟩
        refine ⟨hbound, ?_⟩
        simpa [Signature.nodePortsExcept, portEntry] using hlabelEq
      have haligned :=
        append_pointwise_relation
          (R := fun id label =>
            ∃ hbound : id < (st.endpoints ++ Sig.nodePorts node).length,
              (st.endpoints ++ Sig.nodePorts node).get
                ⟨id, hbound⟩ = label)
          hrest
          (by
            simp [Signature.nodePortsExcept, nodeEndpoints,
              Signature.nodePorts, eraseFin_length])
          hleft hright n hid hfrontier
      rcases haligned with ⟨hbound, hlabelEq⟩
      simpa using hlabelEq
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_left_bound edge hold
        exact old_bound_lift hbound
      · cases hnew
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        exact old_bound_lift hbound
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.edge_right_bound edge hold
        exact old_bound_lift hbound
      · cases hnew
        have hmem :
            nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints entryIdx
        exact fresh_bound_of_mem hmem
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_left_label edge hold
        have hbound := hv.edge_left_bound edge hold
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨edge.left, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨edge.left, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ = edge.leftLabel := hlabel
      · cases hnew
        have hlabel := hv.frontier_head_label hids
        have hbound := hv.frontier_bound activeId (by rw [hids]; simp)
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨activeId, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨activeId, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ = active := hlabel
    · intro edge hmem
      simp at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.edge_right_label edge hold
        have hbound := hv.edge_right_bound edge hold
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨edge.right, old_bound_lift hbound⟩ =
              st.endpoints.get ⟨edge.right, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ = edge.rightLabel := hlabel
      · cases hnew
        have hlabel :=
          freshNodeEndpoints_label_append st hv node entryIdx
            (fresh_bound_of_mem (List.get_mem nodeEndpoints entryIdx))
        simpa [nodeEndpoints, entryIdx, Signature.nodePorts] using hlabel
    · intro renderNode hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact hv.node_incident_length renderNode hold
      · cases hnew
        simp
    · intro renderNode hmem slot
      simp at hmem
      rcases hmem with hold | hnew
      · have hbound := hv.node_incident_bound renderNode hold slot
        exact old_bound_lift hbound
      · cases hnew
        have hmem :
            nodeEndpoints.get slot ∈ nodeEndpoints :=
          List.get_mem nodeEndpoints slot
        exact fresh_bound_of_mem hmem
    · intro renderNode hmem slot
      simp at hmem
      rcases hmem with hold | hnew
      · have hlabel := hv.node_incident_label renderNode hold slot
        have hbound := hv.node_incident_bound renderNode hold slot
        calc
          (st.endpoints ++ Sig.nodePorts node).get
              ⟨renderNode.incident.get slot, old_bound_lift hbound⟩ =
              st.endpoints.get
                ⟨renderNode.incident.get slot, hbound⟩ := by
                exact list_get_append_left st.endpoints
                  (Sig.nodePorts node) hbound (old_bound_lift hbound)
          _ =
              Sig.port renderNode.label
                (Fin.cast (hv.node_incident_length renderNode hold) slot) :=
                hlabel
      · cases hnew
        have hlabel :=
          freshNodeEndpoints_label_append st hv node slot
            (fresh_bound_of_mem (List.get_mem nodeEndpoints slot))
        simpa [nodeEndpoints, Signature.nodePorts] using hlabel

theorem budStep_endpointPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds) (hp : st.EndpointPartition) :
    (budStep node entry ok st).EndpointPartition := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    have oldFrontierNodup : (activeId :: restIds).Nodup := by
      simpa [hids] using hp.frontier_nodup
    have active_not_rest : activeId ∉ restIds := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.1
    have rest_nodup : restIds.Nodup := by
      have hsplit : activeId ∉ restIds ∧ restIds.Nodup := by
        simpa using oldFrontierNodup
      exact hsplit.2
    have active_old_frontier : activeId ∈ st.frontierIds := by
      rw [hids]
      simp
    have active_old_bound : activeId < st.endpoints.length :=
      hv.frontier_bound activeId active_old_frontier
    have entry_mem_fresh : nodeEndpoints.get entryIdx ∈ nodeEndpoints :=
      List.get_mem nodeEndpoints entryIdx
    have entry_fresh_ge : st.nextEndpoint ≤ nodeEndpoints.get entryIdx :=
      freshNodeEndpoints_mem_ge entry_mem_fresh
    have active_ne_entry : activeId ≠ nodeEndpoints.get entryIdx := by
      intro hsame
      have hnext := hv.nextEndpoint_eq
      omega
    dsimp
    let newEdge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := Sig.port node entry
        left := activeId
        right := nodeEndpoints.get entryIdx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    let child : RenderState Sig (frontier ++ Sig.nodePortsExcept node entry) :=
      { nextEndpoint := st.nextEndpoint + Sig.arity node
        endpoints := st.endpoints ++ Sig.nodePorts node
        edges := st.edges ++ [newEdge]
        nodes := st.nodes ++ [{ label := node, incident := nodeEndpoints }]
        frontierIds := restIds ++ eraseFin nodeEndpoints entryIdx
        frontierIds_length := by
          dsimp [nodeEndpoints, entryIdx]
          simp [hrest, Signature.nodePortsExcept, Signature.nodePorts,
            eraseFin_length] }
    change child.EndpointPartition
    have childConsumed_eq :
        child.edgeEndpointIds =
          st.edgeEndpointIds ++ [activeId, nodeEndpoints.get entryIdx] := by
      simp [child, newEdge, RenderState.edgeEndpointIds]
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < child.endpoints.length := by
      simp [child, Signature.nodePorts]
      omega
    have fresh_bound_of_mem {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < child.endpoints.length := by
      have hlt := freshNodeEndpoints_mem_lt
        (by simpa [nodeEndpoints] using hmem)
      have hnext := hv.nextEndpoint_eq
      simp [child, Signature.nodePorts] at hlt ⊢
      omega
    have old_fresh_disjoint
        {id : Nat} (hold : id < st.endpoints.length)
        (hfresh : id ∈ nodeEndpoints) : False := by
      have hge := freshNodeEndpoints_mem_ge
        (by simpa [nodeEndpoints] using hfresh)
      have hnext := hv.nextEndpoint_eq
      omega
    refine
      { frontier_nodup := ?_
        consumed_nodup := ?_
        consumed_bound := ?_
        frontier_consumed_disjoint := ?_
        endpoint_covered := ?_ }
    · apply nodup_append_of_nodup_disjoint
      · exact rest_nodup
      · exact nodup_eraseFin nodeEndpoints entryIdx
          (freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node))
      · intro id hrestMem hfreshExcept
        have hold := hv.frontier_bound id (by
          rw [hids]
          right
          exact hrestMem)
        have hfresh : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hfreshExcept
        exact old_fresh_disjoint hold hfresh
    · have hnodup :
          (st.edgeEndpointIds ++ [activeId, nodeEndpoints.get entryIdx]).Nodup := by
        apply nodup_append_of_nodup_disjoint
        · exact hp.consumed_nodup
        · have hpair :
            ([activeId, nodeEndpoints.get entryIdx] : List Nat).Nodup := by
            simp
            exact active_ne_entry
          exact hpair
        · intro id hold hnew
          simp at hnew
          rcases hnew with hactive | hentry
          · exact hp.frontier_consumed_disjoint id
              (by simpa [hactive] using active_old_frontier) hold
          · have holdBound := hp.consumed_bound id hold
            have hfresh : id ∈ nodeEndpoints := by
              simp [hentry]
            exact old_fresh_disjoint holdBound hfresh
      rw [childConsumed_eq]
      exact hnodup
    · intro id hmem
      rw [childConsumed_eq] at hmem
      simp at hmem
      rcases hmem with hold | hnew
      · exact old_bound_lift (hp.consumed_bound id hold)
      · rcases hnew with hactive | hentry
        · simpa [hactive] using old_bound_lift active_old_bound
        · have hfresh : id ∈ nodeEndpoints := by
            simp [hentry]
          exact fresh_bound_of_mem hfresh
    · intro id hfrontier hconsumed
      rw [childConsumed_eq] at hconsumed
      change id ∈ restIds ++ eraseFin nodeEndpoints entryIdx at hfrontier
      simp at hfrontier
      simp at hconsumed
      rcases hfrontier with hrestMem | hfreshExcept
      · rcases hconsumed with holdConsumed | hnew
        · have oldFrontier : id ∈ st.frontierIds := by
            rw [hids]
            right
            exact hrestMem
          exact hp.frontier_consumed_disjoint id oldFrontier holdConsumed
        · rcases hnew with hactive | hentry
          · exact active_not_rest (by simpa [hactive] using hrestMem)
          · have hold := hv.frontier_bound id (by
              rw [hids]
              right
              exact hrestMem)
            have hfresh : id ∈ nodeEndpoints := by
              simp [hentry]
            exact old_fresh_disjoint hold hfresh
      · have hfresh : id ∈ nodeEndpoints :=
          mem_of_mem_eraseFin nodeEndpoints entryIdx hfreshExcept
        rcases hconsumed with holdConsumed | hnew
        · have holdBound := hp.consumed_bound id holdConsumed
          exact old_fresh_disjoint holdBound hfresh
        · rcases hnew with hactive | hentry
          · have hold := active_old_bound
            have hactiveEq : id = activeId := hactive
            exact old_fresh_disjoint (by simpa [hactiveEq]) hfresh
          · have hentryNotMem :
              nodeEndpoints.get entryIdx ∉ eraseFin nodeEndpoints entryIdx :=
              get_not_mem_eraseFin_of_nodup nodeEndpoints entryIdx
                (freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node))
            exact hentryNotMem (by simpa [hentry] using hfreshExcept)
    · intro id hid
      by_cases hold : id < st.endpoints.length
      · rcases hp.endpoint_covered id hold with holdFrontier | holdConsumed
        · rw [hids] at holdFrontier
          simp at holdFrontier
          rcases holdFrontier with hactive | hrestMem
          · right
            rw [childConsumed_eq]
            simp [hactive]
          · left
            change id ∈ restIds ++ eraseFin nodeEndpoints entryIdx
            simp [hrestMem]
        · right
          rw [childConsumed_eq]
          simp [holdConsumed]
      · have hge : st.endpoints.length ≤ id := Nat.le_of_not_gt hold
        have hnext := hv.nextEndpoint_eq
        have hfresh : id ∈ nodeEndpoints := by
          apply freshNodeEndpoints_mem_of_bounds
          · omega
          · have hchildLen :
                child.endpoints.length =
                  st.endpoints.length + Sig.arity node := by
              simp [child, Signature.nodePorts]
            have hid' := hid
            rw [hchildLen] at hid'
            omega
        by_cases hentry : id = nodeEndpoints.get entryIdx
        · right
          rw [childConsumed_eq]
          simp [hentry]
        · left
          change id ∈ restIds ++ eraseFin nodeEndpoints entryIdx
          simp
          right
          exact mem_eraseFin_of_mem_ne_get nodeEndpoints entryIdx hfresh hentry

theorem budStep_nodeIncidentNodup {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hn : st.NodeIncidentNodup) :
    (budStep node entry ok st).NodeIncidentNodup := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i _activeId _restIds _hids
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    constructor
    intro renderNode hmem
    simp at hmem
    rcases hmem with hold | hnew
    · exact hn.node_incident_nodup renderNode hold
    · cases hnew
      exact freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node)

theorem budStep_ownerIdPartition {active : Sig.Port}
    {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier))
    (hv : st.ValidIds)
    {boundary : List Sig.Port}
    (ho : st.OwnerIdPartition boundary) :
    (budStep node entry ok st).OwnerIdPartition boundary := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rename_i activeId restIds hids
    have hrest : restIds.length = frontier.length := by
      have hlen := st.frontierIds_length
      rw [hids] at hlen
      simpa using Nat.succ.inj hlen
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    let child : RenderState Sig (frontier ++ Sig.nodePortsExcept node entry) :=
      { nextEndpoint := st.nextEndpoint + Sig.arity node
        endpoints := st.endpoints ++ Sig.nodePorts node
        edges := st.edges ++
          [{ label := Sig.portEdge active
             leftLabel := active
             rightLabel := Sig.port node entry
             left := activeId
             right := nodeEndpoints.get entryIdx
             left_label := rfl
             right_label := (Sig.compatible_edge ok).symm
             compatible := ok }]
        nodes := st.nodes ++ [{ label := node, incident := nodeEndpoints }]
        frontierIds := restIds ++ eraseFin nodeEndpoints entryIdx
        frontierIds_length := by
          dsimp [nodeEndpoints, entryIdx]
          simp [hrest, Signature.nodePortsExcept, Signature.nodePorts,
            eraseFin_length] }
    change child.OwnerIdPartition boundary
    have childOwners_eq :
        child.ownerEndpointIds boundary =
          st.ownerEndpointIds boundary ++ nodeEndpoints := by
      simp [child, RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
    have childEndpoints_len :
        child.endpoints.length = st.endpoints.length + Sig.arity node := by
      simp [child, Signature.nodePorts]
    have old_bound_lift {id : Nat} (hbound : id < st.endpoints.length) :
        id < child.endpoints.length := by
      rw [childEndpoints_len]
      omega
    have fresh_bound {id : Nat} (hmem : id ∈ nodeEndpoints) :
        id < child.endpoints.length := by
      have hlt := freshNodeEndpoints_mem_lt
        (by simpa [nodeEndpoints] using hmem)
      have hnext := hv.nextEndpoint_eq
      rw [childEndpoints_len]
      simp at hlt
      omega
    have old_fresh_disjoint {id : Nat}
        (hold : id ∈ st.ownerEndpointIds boundary)
        (hfresh : id ∈ nodeEndpoints) : False := by
      have holdBound := ho.owner_bound id hold
      have hge := freshNodeEndpoints_mem_ge
        (by simpa [nodeEndpoints] using hfresh)
      have hnext := hv.nextEndpoint_eq
      omega
    refine
      { owner_nodup := ?_
        owner_bound := ?_
        owner_covered := ?_ }
    · rw [childOwners_eq]
      apply nodup_append_of_nodup_disjoint
      · exact ho.owner_nodup
      · exact freshNodeEndpoints_nodup st.nextEndpoint (Sig.arity node)
      · intro id hold hfresh
        exact old_fresh_disjoint hold hfresh
    · intro id hmem
      rw [childOwners_eq] at hmem
      simp at hmem
      rcases hmem with hold | hfresh
      · exact old_bound_lift (ho.owner_bound id hold)
      · exact fresh_bound hfresh
    · intro id hid
      by_cases hold : id < st.endpoints.length
      · have holdOwner := ho.owner_covered id hold
        rw [childOwners_eq]
        exact List.mem_append_left nodeEndpoints holdOwner
      · have hge : st.endpoints.length ≤ id := Nat.le_of_not_gt hold
        have hfresh : id ∈ nodeEndpoints := by
          apply freshNodeEndpoints_mem_of_bounds
          · have hnext := hv.nextEndpoint_eq
            simp
            omega
          · have hid' := hid
            rw [childEndpoints_len] at hid'
            have hnext := hv.nextEndpoint_eq
            simp
            omega
        rw [childOwners_eq]
        exact List.mem_append_right (st.ownerEndpointIds boundary) hfresh

/--
Execute traversal syntax into a construction trace.

This is not yet the final semantic quotient bridge: it is the concrete
frontier-processing pass that the bridge uses to build a finished
`PortHypergraph`.
-/
def renderTrace :
    ∀ {frontier : List Sig.Port}, Diag Sig frontier → RenderState Sig frontier →
      RenderState Sig []
  | [], finish, st =>
      { nextEndpoint := st.nextEndpoint
        endpoints := st.endpoints
        edges := st.edges
        nodes := st.nodes
        frontierIds := []
        frontierIds_length := rfl }
  | _active :: _frontier, connect mate ok child, st =>
      renderTrace child (connectStep mate ok st)
  | _active :: _frontier, bud node entry ok child, st =>
      renderTrace child (budStep node entry ok st)

theorem renderTrace_validIds :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      st.ValidIds → (renderTrace d st).ValidIds
  | [], finish, st, hv => by
      dsimp [renderTrace]
      refine
        { nextEndpoint_eq := hv.nextEndpoint_eq
          frontier_bound := ?_
          frontier_label := ?_
          edge_left_bound := hv.edge_left_bound
          edge_right_bound := hv.edge_right_bound
          edge_left_label := hv.edge_left_label
          edge_right_label := hv.edge_right_label
          node_incident_length := hv.node_incident_length
          node_incident_bound := hv.node_incident_bound
          node_incident_label := hv.node_incident_label }
      · intro id hmem
        cases hmem
      · intro n hid _hfrontier
        cases hid
  | _active :: _frontier, connect mate ok child, st, hv =>
      renderTrace_validIds child (connectStep mate ok st)
        (connectStep_validIds mate ok st hv)
  | _active :: _frontier, bud node entry ok child, st, hv =>
      renderTrace_validIds child (budStep node entry ok st)
        (budStep_validIds node entry ok st hv)

theorem renderTrace_endpointPartition :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      st.ValidIds → st.EndpointPartition →
        (renderTrace d st).EndpointPartition
  | [], finish, st, _hv, hp => by
      dsimp [renderTrace]
      refine
        { frontier_nodup := ?_
          consumed_nodup := ?_
          consumed_bound := ?_
          frontier_consumed_disjoint := ?_
          endpoint_covered := ?_ }
      · simp
      · simpa [RenderState.edgeEndpointIds] using hp.consumed_nodup
      · intro id hmem
        exact hp.consumed_bound id (by
          simpa [RenderState.edgeEndpointIds] using hmem)
      · intro id hfrontier _hconsumed
        cases hfrontier
      · intro id hid
        right
        simpa [RenderState.edgeEndpointIds] using
          (RenderState.EndpointPartition.endpoint_consumed_of_frontier_empty
            hp ⟨id, hid⟩)
  | _active :: _frontier, connect mate ok child, st, hv, hp =>
      renderTrace_endpointPartition child (connectStep mate ok st)
        (connectStep_validIds mate ok st hv)
        (connectStep_endpointPartition mate ok st hv hp)
  | _active :: _frontier, bud node entry ok child, st, hv, hp =>
      renderTrace_endpointPartition child (budStep node entry ok st)
        (budStep_validIds node entry ok st hv)
        (budStep_endpointPartition node entry ok st hv hp)

theorem renderTrace_nodeIncidentNodup :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      st.NodeIncidentNodup → (renderTrace d st).NodeIncidentNodup
  | [], finish, st, hn => by
      dsimp [renderTrace]
      constructor
      intro node hmem
      exact hn.node_incident_nodup node hmem
  | _active :: _frontier, connect mate ok child, st, hn =>
      renderTrace_nodeIncidentNodup child (connectStep mate ok st)
        (connectStep_nodeIncidentNodup mate ok st hn)
  | _active :: _frontier, bud node entry ok child, st, hn =>
      renderTrace_nodeIncidentNodup child (budStep node entry ok st)
        (budStep_nodeIncidentNodup node entry ok st hn)

theorem renderTrace_ownerIdPartition :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) (boundary : List Sig.Port),
      st.ValidIds → st.OwnerIdPartition boundary →
        (renderTrace d st).OwnerIdPartition boundary
  | [], finish, st, boundary, _hv, ho => by
      dsimp [renderTrace]
      refine
        { owner_nodup := ?_
          owner_bound := ?_
          owner_covered := ?_ }
      · simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
          using ho.owner_nodup
      · intro id hmem
        exact ho.owner_bound id (by
          simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
            using hmem)
      · intro id hid
        simpa [RenderState.ownerEndpointIds, RenderState.nodeIncidentIds]
          using ho.owner_covered id hid
  | _active :: _frontier, connect mate ok child, st, boundary, hv, ho =>
      renderTrace_ownerIdPartition child (connectStep mate ok st) boundary
        (connectStep_validIds mate ok st hv)
        (connectStep_ownerIdPartition mate ok st ho)
  | _active :: _frontier, bud node entry ok child, st, boundary, hv, ho =>
      renderTrace_ownerIdPartition child (budStep node entry ok st) boundary
        (budStep_validIds node entry ok st hv)
        (budStep_ownerIdPartition node entry ok st hv ho)

theorem renderTrace_reachability :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) {boundary : List Sig.Port},
      st.Reachability boundary → (renderTrace d st).Reachability boundary
  | [], finish, st, _boundary, hr => by
      dsimp [renderTrace]
      refine
        { frontier_reaches := ?_
          node_reaches := ?_ }
      · intro id hmem
        cases hmem
      · intro node hmem
        rcases hr.node_reaches node hmem with ⟨slot, reach⟩
        refine ⟨slot, ?_⟩
        exact RenderState.RawReachesBoundary.mono
          (st := st)
          (st' :=
            { nextEndpoint := st.nextEndpoint
              endpoints := st.endpoints
              edges := st.edges
              nodes := st.nodes
              frontierIds := []
              frontierIds_length := rfl })
          (fun _edge hmem => hmem)
          (fun _node hmem => hmem)
          reach
  | _active :: _frontier, connect mate ok child, st, _boundary, hr =>
      renderTrace_reachability child (connectStep mate ok st)
        (connectStep_reachability mate ok st hr)
  | _active :: _frontier, bud node entry ok child, st, _boundary, hr =>
      renderTrace_reachability child (budStep node entry ok st)
        (budStep_reachability node entry ok st hr)

theorem renderTrace_connect
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier)) :
    renderTrace (Diag.connect mate ok child) st =
      renderTrace child (connectStep mate ok st) :=
  rfl

theorem renderTrace_bud
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    renderTrace (Diag.bud node entry ok child) st =
      renderTrace child (budStep node entry ok st) :=
  rfl

/-- Edges already present before rendering a syntax subtree remain present in
the completed render trace. -/
theorem renderTrace_edge_mem_old :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) {edge : RenderEdge Sig},
      edge ∈ st.edges → edge ∈ (renderTrace d st).edges
  | [], finish, st, edge, hmem => by
      simpa [renderTrace] using hmem
  | _active :: _frontier, connect mate ok child, st, edge, hmem => by
      rw [renderTrace_connect]
      exact renderTrace_edge_mem_old child (connectStep mate ok st)
        (connectStep_edge_mem_old mate ok st hmem)
  | _active :: _frontier, bud node entry ok child, st, edge, hmem => by
      rw [renderTrace_bud]
      exact renderTrace_edge_mem_old child (budStep node entry ok st)
        (budStep_edge_mem_old node entry ok st hmem)

/-- Constructor nodes already present before rendering a syntax subtree remain
present in the completed render trace. -/
theorem renderTrace_node_mem_old :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier) {node : RenderNode Sig},
      node ∈ st.nodes → node ∈ (renderTrace d st).nodes
  | [], finish, st, node, hmem => by
      simpa [renderTrace] using hmem
  | _active :: _frontier, connect mate ok child, st, node, hmem => by
      rw [renderTrace_connect]
      exact renderTrace_node_mem_old child (connectStep mate ok st)
        (connectStep_node_mem_old mate ok st hmem)
  | _active :: _frontier, bud ctor entry ok child, st, node, hmem => by
      rw [renderTrace_bud]
      exact renderTrace_node_mem_old child (budStep ctor entry ok st)
        (budStep_node_mem_old ctor entry ok st hmem)

/-- The concrete edge introduced by a top-level `connect` remains present after
rendering the child diagram. -/
theorem renderTrace_connect_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := frontier.get mate
       left := activeId
       right :=
        restIds.get (Fin.cast (by
          have hlen := st.frontierIds_length
          rw [hids] at hlen
          exact (Nat.succ.inj hlen).symm) mate)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (renderTrace (Diag.connect mate ok child) st).edges := by
  rw [renderTrace_connect]
  exact renderTrace_edge_mem_old child (connectStep mate ok st)
    (connectStep_new_edge_mem mate ok st hids)

/-- The concrete edge introduced by a top-level `bud` remains present after
rendering the child diagram. -/
theorem renderTrace_bud_edge_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    ({ label := Sig.portEdge active
       leftLabel := active
       rightLabel := Sig.port node entry
       left := activeId
       right :=
        (freshNodeEndpoints st.nextEndpoint (Sig.arity node)).get
          (Fin.cast (by simp [freshNodeEndpoints]) entry)
       left_label := rfl
       right_label := (Sig.compatible_edge ok).symm
       compatible := ok } : RenderEdge Sig) ∈
      (renderTrace (Diag.bud node entry ok child) st).edges := by
  rw [renderTrace_bud]
  exact renderTrace_edge_mem_old child (budStep node entry ok st)
    (budStep_new_edge_mem node entry ok st hids)

/-- The concrete constructor node introduced by a top-level `bud` remains
present after rendering the child diagram. -/
theorem renderTrace_bud_node_mem
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    ({ label := node
       incident := freshNodeEndpoints st.nextEndpoint (Sig.arity node) } :
        RenderNode Sig) ∈
      (renderTrace (Diag.bud node entry ok child) st).nodes := by
  rw [renderTrace_bud]
  exact renderTrace_node_mem_old child (budStep node entry ok st)
    (budStep_new_node_mem node entry ok st)

theorem connectStep_edgesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderEdge Sig),
      (connectStep mate ok st).edges = st.edges ++ suffix := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[_], rfl⟩

theorem budStep_edgesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderEdge Sig),
      (budStep node entry ok st).edges = st.edges ++ suffix := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[_], rfl⟩

/--
Edges already in a render state remain an ordered prefix of the completed
render trace.  The recursive bridge uses this stronger prefix fact, not just
membership, to identify processed edge indices after a render prefix.
-/
theorem renderTrace_edgesPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      ∃ suffix : List (RenderEdge Sig),
        (renderTrace d st).edges = st.edges ++ suffix
  | [], finish, st => by
      refine ⟨[], ?_⟩
      simp [renderTrace]
  | _active :: _frontier, connect mate ok child, st => by
      rcases renderTrace_edgesPrefix child (connectStep mate ok st) with
        ⟨suffix, hsuffix⟩
      rcases connectStep_edgesPrefix mate ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_connect, hsuffix, hstep, List.append_assoc]
  | _active :: _frontier, bud node entry ok child, st => by
      rcases renderTrace_edgesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      rcases budStep_edgesPrefix node entry ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_bud, hsuffix, hstep, List.append_assoc]

/--
The edge introduced by a top-level rendered `connect` is at the first edge
index after the render prefix.  This deterministic index fact is needed to
relate renderer prefixes to traversal `processedEdges`.
-/
theorem renderTrace_connect_new_edge_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.connect mate ok child) st
    let mateId :=
      restIds.get (Fin.cast (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        exact (Nat.succ.inj hlen).symm) mate)
    let edge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := frontier.get mate
        left := activeId
        right := mateId
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    final.edges.get ⟨st.edges.length, by
      dsimp [final]
      rcases renderTrace_edgesPrefix child (connectStep mate ok st) with
        ⟨suffix, hsuffix⟩
      have hstep :
          (connectStep mate ok st).edges = st.edges ++ [edge] := by
        unfold connectStep
        split
        · rename_i hnil
          exact False.elim (RenderState.frontierIds_ne_nil st hnil)
        · rename_i activeId' restIds' hids'
          rw [hids] at hids'
          injection hids' with hactive hrest
          subst activeId'
          subst restIds'
          simp [edge, mateId]
      rw [renderTrace_connect, hsuffix, hstep]
      simp⟩ = edge := by
  intro final mateId edge
  rcases renderTrace_edgesPrefix child (connectStep mate ok st) with
    ⟨suffix, hsuffix⟩
  have hstep :
      (connectStep mate ok st).edges = st.edges ++ [edge] := by
    unfold connectStep
    split
    · rename_i hnil
      exact False.elim (RenderState.frontierIds_ne_nil st hnil)
    · rename_i activeId' restIds' hids'
      rw [hids] at hids'
      injection hids' with hactive hrest
      subst activeId'
      subst restIds'
      simp [edge, mateId]
  have hfinal :
      final.edges = st.edges ++ edge :: suffix := by
    dsimp [final]
    rw [renderTrace_connect, hsuffix, hstep]
    simp
  have hbound : st.edges.length < final.edges.length := by
    rw [hfinal]
    simp
  have hidx :
      (⟨st.edges.length, by
        dsimp [final]
        rw [renderTrace_connect, hsuffix, hstep]
        simp⟩ : Fin final.edges.length) =
      ⟨st.edges.length, hbound⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hopt :
      final.edges[st.edges.length]? = some edge := by
    rw [hfinal]
    simp
  have hsome :
      final.edges[st.edges.length]? =
        some (final.edges.get ⟨st.edges.length, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  rw [hsome] at hopt
  injection hopt with hget

/--
The edge introduced by a top-level rendered `bud` is at the first edge index
after the render prefix.  This is the bud analogue of
`renderTrace_connect_new_edge_get`.
-/
theorem renderTrace_bud_new_edge_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.bud node entry ok child) st
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let entryIdx : Fin nodeEndpoints.length :=
      Fin.cast (by simp [nodeEndpoints]) entry
    let edge : RenderEdge Sig :=
      { label := Sig.portEdge active
        leftLabel := active
        rightLabel := Sig.port node entry
        left := activeId
        right := nodeEndpoints.get entryIdx
        left_label := rfl
        right_label := (Sig.compatible_edge ok).symm
        compatible := ok }
    final.edges.get ⟨st.edges.length, by
      dsimp [final]
      rcases renderTrace_edgesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      have hstep :
          (budStep node entry ok st).edges = st.edges ++ [edge] := by
        unfold budStep
        split
        · rename_i hnil
          exact False.elim (RenderState.frontierIds_ne_nil st hnil)
        · rename_i activeId' restIds' hids'
          rw [hids] at hids'
          injection hids' with hactive hrest
          subst activeId'
          subst restIds'
          simp [edge, nodeEndpoints, entryIdx]
      rw [renderTrace_bud, hsuffix, hstep]
      simp⟩ = edge := by
  intro final nodeEndpoints entryIdx edge
  rcases renderTrace_edgesPrefix child (budStep node entry ok st) with
    ⟨suffix, hsuffix⟩
  have hstep :
      (budStep node entry ok st).edges = st.edges ++ [edge] := by
    unfold budStep
    split
    · rename_i hnil
      exact False.elim (RenderState.frontierIds_ne_nil st hnil)
    · rename_i activeId' restIds' hids'
      rw [hids] at hids'
      injection hids' with hactive hrest
      subst activeId'
      subst restIds'
      simp [edge, nodeEndpoints, entryIdx]
  have hfinal :
      final.edges = st.edges ++ edge :: suffix := by
    dsimp [final]
    rw [renderTrace_bud, hsuffix, hstep]
    simp
  have hbound : st.edges.length < final.edges.length := by
    rw [hfinal]
    simp
  have hidx :
      (⟨st.edges.length, by
        dsimp [final]
        rw [renderTrace_bud, hsuffix, hstep]
        simp⟩ : Fin final.edges.length) =
      ⟨st.edges.length, hbound⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hopt :
      final.edges[st.edges.length]? = some edge := by
    rw [hfinal]
    simp
  have hsome :
      final.edges[st.edges.length]? =
        some (final.edges.get ⟨st.edges.length, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  rw [hsome] at hopt
  injection hopt with hget

theorem connectStep_nodesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderNode Sig),
      (connectStep mate ok st).nodes = st.nodes ++ suffix := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[], by simp⟩

theorem budStep_nodesPrefix
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    ∃ suffix : List (RenderNode Sig),
      (budStep node entry ok st).nodes = st.nodes ++ suffix := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · exact ⟨[_], rfl⟩

/--
Constructor nodes already in a render state remain an ordered prefix of the
completed render trace.  The recursive bridge uses this to identify seen-node
indices after a render prefix.
-/
theorem renderTrace_nodesPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      ∃ suffix : List (RenderNode Sig),
        (renderTrace d st).nodes = st.nodes ++ suffix
  | [], finish, st => by
      refine ⟨[], ?_⟩
      simp [renderTrace]
  | _active :: _frontier, connect mate ok child, st => by
      rcases renderTrace_nodesPrefix child (connectStep mate ok st) with
        ⟨suffix, hsuffix⟩
      rcases connectStep_nodesPrefix mate ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_connect, hsuffix, hstep, List.append_assoc]
  | _active :: _frontier, bud node entry ok child, st => by
      rcases renderTrace_nodesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      rcases budStep_nodesPrefix node entry ok st with
        ⟨stepSuffix, hstep⟩
      refine ⟨stepSuffix ++ suffix, ?_⟩
      rw [renderTrace_bud, hsuffix, hstep, List.append_assoc]

/--
The constructor node introduced by a top-level rendered `bud` is at the first
node index after the render prefix.  This deterministic index fact is needed
to relate renderer prefixes to traversal `seenNodes`.
-/
theorem renderTrace_bud_new_node_get
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier)) :
    let final := renderTrace (Diag.bud node entry ok child) st
    let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
    let renderNode : RenderNode Sig :=
      { label := node
        incident := nodeEndpoints }
    final.nodes.get ⟨st.nodes.length, by
      dsimp [final]
      rcases renderTrace_nodesPrefix child (budStep node entry ok st) with
        ⟨suffix, hsuffix⟩
      have hstep :
          (budStep node entry ok st).nodes = st.nodes ++ [renderNode] := by
        unfold budStep
        split
        · rename_i hnil
          exact False.elim (RenderState.frontierIds_ne_nil st hnil)
        · simp [renderNode, nodeEndpoints]
      rw [renderTrace_bud, hsuffix, hstep]
      simp⟩ = renderNode := by
  intro final nodeEndpoints renderNode
  rcases renderTrace_nodesPrefix child (budStep node entry ok st) with
    ⟨suffix, hsuffix⟩
  have hstep :
      (budStep node entry ok st).nodes = st.nodes ++ [renderNode] := by
    unfold budStep
    split
    · rename_i hnil
      exact False.elim (RenderState.frontierIds_ne_nil st hnil)
    · simp [renderNode, nodeEndpoints]
  have hfinal :
      final.nodes = st.nodes ++ renderNode :: suffix := by
    dsimp [final]
    rw [renderTrace_bud, hsuffix, hstep]
    simp
  have hbound : st.nodes.length < final.nodes.length := by
    rw [hfinal]
    simp
  have hidx :
      (⟨st.nodes.length, by
        dsimp [final]
        rw [renderTrace_bud, hsuffix, hstep]
        simp⟩ : Fin final.nodes.length) =
      ⟨st.nodes.length, hbound⟩ := by
    apply Fin.ext
    rfl
  rw [hidx]
  have hopt :
      final.nodes[st.nodes.length]? = some renderNode := by
    rw [hfinal]
    simp
  have hsome :
      final.nodes[st.nodes.length]? =
        some (final.nodes.get ⟨st.nodes.length, hbound⟩) :=
    List.getElem?_eq_getElem hbound
  rw [hsome] at hopt
  injection hopt with hget

theorem connectStep_edges_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).edges.length = st.edges.length + 1 := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp

theorem connectStep_nodes
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).nodes = st.nodes := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rfl

theorem connectStep_endpoints
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (st : RenderState Sig (active :: frontier)) :
    (connectStep mate ok st).endpoints = st.endpoints := by
  unfold connectStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rfl

theorem budStep_endpoints
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).endpoints =
      st.endpoints ++ Sig.nodePorts node := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · rfl

theorem budStep_edges_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).edges.length = st.edges.length + 1 := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp

theorem budStep_nodes_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).nodes.length = st.nodes.length + 1 := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp

theorem budStep_endpoints_length
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (st : RenderState Sig (active :: frontier)) :
    (budStep node entry ok st).endpoints.length =
      st.endpoints.length + Sig.arity node := by
  unfold budStep
  split
  · rename_i hids
    exact False.elim (RenderState.frontierIds_ne_nil st hids)
  · simp [Signature.nodePorts]

def renderTrace_endpointPrefix :
    ∀ {frontier : List Sig.Port} (d : Diag Sig frontier)
      (st : RenderState Sig frontier),
      RenderState.EndpointPrefix (renderTrace d st) st.endpoints
  | [], finish, st =>
      { suffix := []
        endpoints_eq := by
          simp [renderTrace] }
  | _active :: _frontier, connect mate ok child, st =>
      let childPrefix :=
        renderTrace_endpointPrefix child (connectStep mate ok st)
      let suffix := childPrefix.suffix
      { suffix := suffix
        endpoints_eq := by
          rw [renderTrace_connect]
          have hchild :
              (renderTrace child (connectStep mate ok st)).endpoints =
                (connectStep mate ok st).endpoints ++ suffix := by
            simpa [suffix] using childPrefix.endpoints_eq
          calc
            (renderTrace child (connectStep mate ok st)).endpoints =
                (connectStep mate ok st).endpoints ++ suffix :=
              hchild
            _ = st.endpoints ++ suffix := by
              rw [connectStep_endpoints] }
  | _active :: _frontier, bud node entry ok child, st =>
      let childPrefix :=
        renderTrace_endpointPrefix child (budStep node entry ok st)
      let suffix := childPrefix.suffix
      { suffix := Sig.nodePorts node ++ suffix
        endpoints_eq := by
          rw [renderTrace_bud]
          have hchild :
              (renderTrace child (budStep node entry ok st)).endpoints =
                (budStep node entry ok st).endpoints ++ suffix := by
            simpa [suffix] using childPrefix.endpoints_eq
          calc
            (renderTrace child (budStep node entry ok st)).endpoints =
                (budStep node entry ok st).endpoints ++ suffix :=
              hchild
            _ =
                (st.endpoints ++ Sig.nodePorts node) ++ suffix := by
              rw [budStep_endpoints]
            _ =
                st.endpoints ++ (Sig.nodePorts node ++ suffix) := by
              rw [List.append_assoc] }

def renderTraceFromBoundary {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState Sig [] :=
  renderTrace d (RenderState.initial Sig boundary)

def renderTraceFromBoundary_endpointPrefix
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.EndpointPrefix (renderTraceFromBoundary d) boundary :=
  let pref := renderTrace_endpointPrefix d (RenderState.initial Sig boundary)
  { suffix := pref.suffix
    endpoints_eq := by
      simpa [renderTraceFromBoundary, RenderState.initial] using
        pref.endpoints_eq }

theorem renderTraceFromBoundary_validIds
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).ValidIds :=
  renderTrace_validIds d (RenderState.initial Sig boundary)
    (RenderState.initial_validIds boundary)

theorem renderTraceFromBoundary_endpointPartition
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).EndpointPartition :=
  renderTrace_endpointPartition d (RenderState.initial Sig boundary)
    (RenderState.initial_validIds boundary)
    (RenderState.initial_endpointPartition boundary)

theorem renderTraceFromBoundary_nodeIncidentNodup
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).NodeIncidentNodup :=
  renderTrace_nodeIncidentNodup d (RenderState.initial Sig boundary)
    (RenderState.initial_nodeIncidentNodup boundary)

theorem renderTraceFromBoundary_ownerIdPartition
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).OwnerIdPartition boundary :=
  renderTrace_ownerIdPartition d (RenderState.initial Sig boundary) boundary
    (RenderState.initial_validIds boundary)
    (RenderState.initial_ownerIdPartition boundary)

theorem renderTraceFromBoundary_reachability
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).Reachability boundary :=
  renderTrace_reachability d (RenderState.initial Sig boundary)
    (RenderState.initial_reachability boundary)

def renderTraceFromBoundary_endpointEdgeEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.EndpointEdgeEvidence (renderTraceFromBoundary d) :=
  RenderState.endpointEdgeEvidenceOfPartition
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_endpointPartition d)

def renderTraceFromBoundary_endpointEdge
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    Fin (renderTraceFromBoundary d).endpoints.length →
      Fin (renderTraceFromBoundary d).edges.length :=
  (renderTraceFromBoundary_endpointEdgeEvidence d).endpointEdge

theorem renderTraceFromBoundary_endpoint_edge_label
    {boundary : List Sig.Port} (d : Diag Sig boundary)
    (endpoint : Fin (renderTraceFromBoundary d).endpoints.length) :
    Sig.portEdge ((renderTraceFromBoundary d).endpoints.get endpoint) =
      ((renderTraceFromBoundary d).edges.get
        (renderTraceFromBoundary_endpointEdge d endpoint)).label :=
  (renderTraceFromBoundary_endpointEdgeEvidence d).endpoint_edge_label endpoint

def renderTraceFromBoundary_edgeEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.EdgeEvidence (renderTraceFromBoundary d) :=
  RenderState.edgeEvidenceOfPartition
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_endpointPartition d)

def renderTraceFromBoundary_boundaryEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.BoundaryEvidence (renderTraceFromBoundary d) boundary :=
  RenderState.boundaryEvidenceOfPrefix
    (renderTraceFromBoundary_endpointPrefix d)

def renderTraceFromBoundary_incidenceEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.IncidenceEvidence (renderTraceFromBoundary d) :=
  RenderState.incidenceEvidenceOfValidIds
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_nodeIncidentNodup d)

theorem renderTraceFromBoundary_frontier_empty
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    (renderTraceFromBoundary d).frontierIds = [] := by
  have hlen := (renderTraceFromBoundary d).frontierIds_length
  cases hids : (renderTraceFromBoundary d).frontierIds with
  | nil => rfl
  | cons _head _tail =>
      rw [hids] at hlen
      simp at hlen

end Diag

structure ConnectParam (Sig : Signature) where
  active : Sig.Port
  frontier : List Sig.Port
  mate : Fin frontier.length
  ok : Sig.compatible active (frontier.get mate)

structure BudParam (Sig : Signature) where
  active : Sig.Port
  frontier : List Sig.Port
  node : Sig.Node
  entry : Fin (Sig.arity node)
  ok : Sig.compatible active (Sig.port node entry)

def Param (Sig : Signature) : Ctor → Type
  | .finish => Unit
  | .connect => ConnectParam Sig
  | .bud => BudParam Sig

def out (Sig : Signature) : (c : Ctor) → Param Sig c → List Sig.Port
  | .finish, _ => []
  | .connect, p => p.active :: p.frontier
  | .bud, p => p.active :: p.frontier

def Pos (_Sig : Signature) : (c : Ctor) → Param _Sig c → Type
  | .finish, _ => Empty
  | .connect, _ => Unit
  | .bud, _ => Unit

def input (Sig : Signature) :
    {c : Ctor} → (p : Param Sig c) → Pos Sig c p → List Sig.Port
  | .finish, _, q => nomatch q
  | .connect, p, _ => eraseFin p.frontier p.mate
  | .bud, p, _ => p.frontier ++ Sig.nodePortsExcept p.node p.entry

/-- Dependent polynomial for typed ordered-frontier traversal syntax. -/
def poly (Sig : Signature) : DepPoly (List Sig.Port) where
  Ctor := Ctor
  Param := Param Sig
  out := out Sig
  Pos := Pos Sig
  input := input Sig

/-- Same-fiber constructor data for typed string diagrams. -/
def inversion (Sig : Signature) : OutputIndexInversion (poly Sig) :=
  OutputIndexInversion.canonical (poly Sig)

def layerToSyntax (Sig : Signature) (boundary : List Sig.Port) :
    CodeLayer (poly Sig) (inversion Sig) (Diag Sig) boundary → Diag Sig boundary
  | ⟨⟨.finish, (), h⟩, _child⟩ => by
      cases h
      exact .finish
  | ⟨⟨.connect, p, h⟩, child⟩ => by
      cases p with
      | mk active frontier mate ok =>
          cases h
          exact .connect mate ok (child ())
  | ⟨⟨.bud, p, h⟩, child⟩ => by
      cases p with
      | mk active frontier node entry ok =>
          cases h
          exact .bud node entry ok (child ())

def syntaxToLayer (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary → CodeLayer (poly Sig) (inversion Sig) (Diag Sig) boundary
  | .finish =>
      ⟨⟨Ctor.finish, (), rfl⟩, fun q => nomatch q⟩
  | @Diag.connect _ active frontier mate ok child =>
      ⟨⟨Ctor.connect, ⟨active, frontier, mate, ok⟩, rfl⟩, fun _ => child⟩
  | @Diag.bud _ active frontier node entry ok child =>
      ⟨⟨Ctor.bud, ⟨active, frontier, node, entry, ok⟩, rfl⟩, fun _ => child⟩

def syntaxLayerPresentation (Sig : Signature) :
    CodeLayerPresentation (poly Sig) (inversion Sig) (Diag Sig) (Diag Sig) :=
  CodeLayerPresentation.ofMaps
    (layerToSyntax Sig)
    (syntaxToLayer Sig)
    (by
      intro boundary layer
      cases layer with
      | mk code child =>
        cases code with
        | mk ctor param out_eq =>
          cases ctor with
          | finish =>
              cases param
              cases out_eq
              have hchild : (fun q => nomatch q) = child := by
                child_eta_empty
              cases hchild
              rfl
          | connect =>
              cases param with
              | mk active frontier mate ok =>
                cases out_eq
                have hchild : (fun _ => child ()) = child := by
                  child_eta_unit
                cases hchild
                rfl
          | bud =>
              cases param with
              | mk active frontier node entry ok =>
                cases out_eq
                have hchild : (fun _ => child ()) = child := by
                  child_eta_unit
                cases hchild
                rfl)
    (by
      intro boundary t
      cases t with
      | finish => rfl
      | connect mate ok child => rfl
      | bud node entry ok child => rfl)

theorem layer_child_rank_lt (Sig : Signature) :
    ∀ {boundary : List Sig.Port} (z : Diag Sig boundary)
      (q : (poly Sig).Pos
          ((inversion Sig).decode boundary
            (((syntaxLayerPresentation Sig).iso boundary).invFun z).1).ctor
          ((inversion Sig).decode boundary
            (((syntaxLayerPresentation Sig).iso boundary).invFun z).1).param),
      Diag.rank ((((syntaxLayerPresentation Sig).iso boundary).invFun z).2 q) <
        Diag.rank z := by
  intro boundary z q
  cases z with
  | finish =>
      cases q
  | connect mate ok child =>
      cases q
      simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMaps,
        syntaxLayerPresentation, syntaxToLayer, inversion,
        OutputIndexInversion.canonical, Diag.rank]
  | bud node entry ok child =>
      cases q
      simp [CodeLayerPresentation.iso, CodeLayerPresentation.ofMaps,
        syntaxLayerPresentation, syntaxToLayer, inversion,
        OutputIndexInversion.canonical, Diag.rank]

/-- Presentation of typed rooted open diagram syntax as generated code data. -/
def syntaxPresentation (Sig : Signature) :
    SyntaxPresentation (poly Sig) (inversion Sig) (Diag Sig) :=
  SyntaxPresentation.ofLayer
    (syntaxLayerPresentation Sig)
    (fun _ t => Diag.rank t)
    (layer_child_rank_lt Sig)

/-- Generated coding data for typed rooted open diagram syntax. -/
def generatedCode (Sig : Signature) : GeneratedCode (poly Sig) (Diag Sig) :=
  (syntaxPresentation Sig).generatedCode

/--
Typed rooted open diagrams are bijective with the initial algebra of their
dependent polynomial presentation through the generic generated-code
construction.
-/
def syntaxIso (Sig : Signature) (boundary : List Sig.Port) :
    Mu (poly Sig) boundary ≃ᵢ Diag Sig boundary :=
  (generatedCode Sig).iso boundary

/-!
## Semantic port-hypergraph representatives

The syntax above uses a frontier of endpoint labels.  The semantic
representative separates those endpoint records from the edges/wires that
connect them: endpoints carry `Sig.Port`, edges carry `Sig.Edge`, and every
endpoint is incident to exactly one edge.  Every endpoint also has exactly one
semantic owner: either one ordered boundary position or one ordered
constructor port.
-/

/-- The unique semantic role played by a graph endpoint. -/
inductive EndpointOwner (boundaryLength nodeCount : Nat)
    (incidentLength : Fin nodeCount → Nat) where
  | boundary : Fin boundaryLength → EndpointOwner boundaryLength nodeCount incidentLength
  | constructor :
      (node : Fin nodeCount) →
      Fin (incidentLength node) →
      EndpointOwner boundaryLength nodeCount incidentLength

/--
A finite typed port-hypergraph representative with an ordered external
boundary.  Endpoints carry endpoint labels, edges carry wire labels, nodes
carry constructor labels, and every constructor incidence points to an ordered
constructor port.  The `endpoint_owner` field is the global monogamy condition
for endpoint ownership: local injectivity is not enough, so each endpoint must
have exactly one boundary-or-constructor owner.
-/
structure PortHypergraph (Sig : Signature) (boundary : List Sig.Port) where
  endpointCount : Nat
  edgeCount : Nat
  nodeCount : Nat
  endpointLabel : Fin endpointCount → Sig.Port
  edgeLabel : Fin edgeCount → Sig.Edge
  endpointEdge : Fin endpointCount → Fin edgeCount
  endpoint_edge_label :
    ∀ endpoint : Fin endpointCount,
      Sig.portEdge (endpointLabel endpoint) = edgeLabel (endpointEdge endpoint)
  edge_compatible :
    ∀ left right : Fin endpointCount,
      endpointEdge left = endpointEdge right →
        left ≠ right →
          Sig.compatible (endpointLabel left) (endpointLabel right)
  edge_two_endpoints :
    ∀ edge : Fin edgeCount,
      ∃ left right : Fin endpointCount,
        left ≠ right ∧
        endpointEdge left = edge ∧
        endpointEdge right = edge ∧
        ∀ endpoint : Fin endpointCount,
          endpointEdge endpoint = edge → endpoint = left ∨ endpoint = right
  boundaryPort : Fin boundary.length → Fin endpointCount
  boundary_injective : Function.Injective boundaryPort
  boundary_label :
    ∀ b : Fin boundary.length, endpointLabel (boundaryPort b) = boundary.get b
  nodeLabel : Fin nodeCount → Sig.Node
  incident : Fin nodeCount → List (Fin endpointCount)
  incident_length :
    ∀ node : Fin nodeCount, (incident node).length = Sig.arity (nodeLabel node)
  incident_injective :
    ∀ node : Fin nodeCount,
      Function.Injective fun slot : Fin (incident node).length =>
        (incident node).get slot
  incidence_label :
    ∀ (node : Fin nodeCount) (slot : Fin (incident node).length),
      endpointLabel ((incident node).get slot) =
        Sig.port (nodeLabel node) (Fin.cast (incident_length node) slot)
  endpoint_owner :
    ∀ endpoint : Fin endpointCount,
      ∃ owner : EndpointOwner boundary.length nodeCount
          (fun node => (incident node).length),
        (match owner with
          | .boundary boundaryIndex => boundaryPort boundaryIndex
          | .constructor node slot => (incident node).get slot) = endpoint ∧
        ∀ owner' : EndpointOwner boundary.length nodeCount
            (fun node => (incident node).length),
          (match owner' with
            | .boundary boundaryIndex => boundaryPort boundaryIndex
            | .constructor node slot => (incident node).get slot) = endpoint →
          owner' = owner

namespace PortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

/-- Interpret an endpoint owner as the endpoint it owns in a concrete graph. -/
def endpointOwnerEndpoint (G : PortHypergraph Sig boundary) :
    EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length) →
      Fin G.endpointCount
  | .boundary boundaryIndex => G.boundaryPort boundaryIndex
  | .constructor node slot => (G.incident node).get slot

/-- The owners of a fixed endpoint.  Valid semantic representatives require
this subtype to have exactly one inhabitant for every endpoint. -/
def endpointOwnersOf (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) : Type :=
  { owner : EndpointOwner boundary.length G.nodeCount
      (fun node => (G.incident node).length) //
    endpointOwnerEndpoint G owner = endpoint }

/-- Every endpoint has exactly one boundary-or-constructor owner. -/
theorem endpointOwnersOf_existsUnique (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    ∃ owner : endpointOwnersOf G endpoint,
      ∀ owner' : endpointOwnersOf G endpoint, owner' = owner := by
  rcases G.endpoint_owner endpoint with ⟨owner, howner, huniq⟩
  have hownerEndpoint : endpointOwnerEndpoint G owner = endpoint := by
    cases owner <;> simpa [endpointOwnerEndpoint] using howner
  refine ⟨⟨owner, hownerEndpoint⟩, ?_⟩
  intro owner'
  rcases owner' with ⟨owner', howner'⟩
  apply Subtype.ext
  apply huniq
  revert howner'
  cases owner' <;> intro howner' <;> simpa [endpointOwnerEndpoint] using howner'

/-- A mate of an endpoint is the other endpoint on the same edge. -/
def EdgeMate (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) : Prop :=
  endpoint ≠ mate ∧ G.endpointEdge endpoint = G.endpointEdge mate

/-- Type-level wrapper for executable edge-mate checks. -/
structure EdgeMateData (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) : Type where
  proof : EdgeMate G endpoint mate

/-- Check whether a concrete endpoint is the edge mate of another endpoint. -/
def edgeMateCandidate? (G : PortHypergraph Sig boundary)
    (endpoint mate : Fin G.endpointCount) :
    Option (EdgeMateData G endpoint mate) :=
  if hsame : endpoint = mate then
    none
  else if hedge : G.endpointEdge endpoint = G.endpointEdge mate then
    some ⟨⟨hsame, hedge⟩⟩
  else
    none

theorem edgeMateCandidate?_isSome_of_edgeMate (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    (edgeMateCandidate? G endpoint mate).isSome := by
  simp [edgeMateCandidate?, hmate.1, hmate.2]

/-- Search the finite endpoint set for the mate of a concrete endpoint. -/
def edgeMateSearch? (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    Option { mate : Fin G.endpointCount // EdgeMate G endpoint mate } :=
  (List.finRange G.endpointCount).findSome? fun mate =>
    match edgeMateCandidate? G endpoint mate with
    | some hmate => some ⟨mate, hmate.proof⟩
    | none => none

/-- Every endpoint has exactly one mate on its edge. -/
theorem edgeMate_existsUnique (G : PortHypergraph Sig boundary)
    (endpoint : Fin G.endpointCount) :
    ∃ mate : Fin G.endpointCount,
      EdgeMate G endpoint mate ∧
        ∀ mate' : Fin G.endpointCount, EdgeMate G endpoint mate' → mate' = mate := by
  rcases G.edge_two_endpoints (G.endpointEdge endpoint) with
    ⟨left, right, hdiff, hleft, hright, hall⟩
  have hendpoint : endpoint = left ∨ endpoint = right := hall endpoint rfl
  rcases hendpoint with hendpoint | hendpoint
  · refine ⟨right, ?_, ?_⟩
    · constructor
      · intro hsame
        exact hdiff (hendpoint.symm.trans hsame)
      · calc
          G.endpointEdge endpoint = G.endpointEdge left := by rw [hendpoint]
          _ = G.endpointEdge right := hleft.trans hright.symm
    · intro mate' hmate'
      rcases hall mate' hmate'.2.symm with hmateLeft | hmateRight
      · have hsame : endpoint = mate' := hendpoint.trans hmateLeft.symm
        exact False.elim (hmate'.1 hsame)
      · exact hmateRight
  · refine ⟨left, ?_, ?_⟩
    · constructor
      · intro hsame
        exact hdiff (hsame.symm.trans hendpoint)
      · calc
          G.endpointEdge endpoint = G.endpointEdge right := by rw [hendpoint]
          _ = G.endpointEdge left := hright.trans hleft.symm
    · intro mate' hmate'
      rcases hall mate' hmate'.2.symm with hmateLeft | hmateRight
      · exact hmateLeft
      · have hsame : endpoint = mate' := hendpoint.trans hmateRight.symm
        exact False.elim (hmate'.1 hsame)

theorem edgeMate_compatible (G : PortHypergraph Sig boundary)
    {endpoint mate : Fin G.endpointCount}
    (hmate : EdgeMate G endpoint mate) :
    Sig.compatible (G.endpointLabel endpoint) (G.endpointLabel mate) :=
  G.edge_compatible endpoint mate hmate.2 hmate.1

theorem incident_nodup (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount) :
    (G.incident node).Nodup :=
  list_nodup_of_get_injective (G.incident node) (G.incident_injective node)

theorem incident_labels (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount) :
    (G.incident node).map G.endpointLabel =
      Sig.nodePorts (G.nodeLabel node) := by
  apply List.ext_getElem
  · simp [Signature.nodePorts, G.incident_length node]
  · intro i hleft hright
    rw [List.getElem_map]
    have hslot : i < (G.incident node).length := by
      simpa using hleft
    have hinc := G.incidence_label node ⟨i, hslot⟩
    simpa [Signature.nodePorts] using hinc

theorem incident_labels_except (G : PortHypergraph Sig boundary)
    (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    (eraseFin (G.incident node) slot).map G.endpointLabel =
      Sig.nodePortsExcept (G.nodeLabel node)
        (Fin.cast (G.incident_length node) slot) := by
  calc
    (eraseFin (G.incident node) slot).map G.endpointLabel =
        eraseFin ((G.incident node).map G.endpointLabel)
          (Fin.cast (by simp) slot) :=
      map_eraseFin G.endpointLabel (G.incident node) slot
    _ = Sig.nodePortsExcept (G.nodeLabel node)
          (Fin.cast (G.incident_length node) slot) := by
      have hlabels := G.incident_labels node
      rw [eraseFin_eq_of_eq hlabels]
      simp [Signature.nodePortsExcept, Signature.nodePorts]

/--
A port endpoint has a path to the ordered boundary when it is a boundary
endpoint, can cross an edge to the other endpoint on that edge, or can move
across the ordered incidences of a constructor already in the same component.
-/
inductive PortReachesBoundary (G : PortHypergraph Sig boundary) :
    Fin G.endpointCount → Prop
  | boundary (b : Fin boundary.length) :
      PortReachesBoundary G (G.boundaryPort b)
  | throughEdge {p q : Fin G.endpointCount}
      (sameEdge : G.endpointEdge p = G.endpointEdge q)
      (different : p ≠ q)
      (reach : PortReachesBoundary G p) :
      PortReachesBoundary G q
  | throughConstructor {p q : Fin G.endpointCount}
      (node : Fin G.nodeCount)
      (fromSlot toSlot : Fin (G.incident node).length)
      (hp : (G.incident node).get fromSlot = p)
      (hq : (G.incident node).get toSlot = q)
      (reach : PortReachesBoundary G p) :
      PortReachesBoundary G q

/-- Every constructor is in some component connected to the external boundary. -/
def AllConstructorsReachBoundary (G : PortHypergraph Sig boundary) : Prop :=
  ∀ node : Fin G.nodeCount,
    ∃ slot : Fin (G.incident node).length,
      PortReachesBoundary G ((G.incident node).get slot)

end PortHypergraph

/--
The semantic representatives for final encoded diagrams: finite typed
port-hypergraphs with ordered external boundary and no constructor in a
component disconnected from that boundary.
-/
structure OpenPortHypergraph (Sig : Signature) (boundary : List Sig.Port) where
  raw : PortHypergraph Sig boundary
  allConstructorsReachBoundary :
    PortHypergraph.AllConstructorsReachBoundary raw

namespace RenderState

variable {Sig : Signature}

/--
Evidence that a completed render trace presents a semantic
`PortHypergraph`.  The trace lists are the storage; this structure supplies
the finite maps and proofs required by the semantic representative.
-/
structure PortHypergraphEvidence
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  edgeEvidence : EdgeEvidence st
  boundaryEvidence : BoundaryEvidence st boundary
  incidenceEvidence : IncidenceEvidence st
  endpoint_owner :
    ∀ endpoint : Fin st.endpoints.length,
      ∃ owner : EndpointOwner boundary.length st.nodes.length
          (fun node => (incidenceEvidence.incident node).length),
        (match owner with
          | .boundary boundaryIndex =>
              boundaryEvidence.boundaryPort boundaryIndex
          | .constructor node slot =>
              (incidenceEvidence.incident node).get slot) = endpoint ∧
        ∀ owner' : EndpointOwner boundary.length st.nodes.length
            (fun node => (incidenceEvidence.incident node).length),
          (match owner' with
            | .boundary boundaryIndex =>
                boundaryEvidence.boundaryPort boundaryIndex
            | .constructor node slot =>
                (incidenceEvidence.incident node).get slot) = endpoint →
          owner' = owner

def portHypergraphEvidenceOfInvariants
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary) :
    PortHypergraphEvidence st boundary where
  edgeEvidence := edgeEvidenceOfPartition hv hp
  boundaryEvidence := boundaryEvidenceOfPrefix pref
  incidenceEvidence := incidenceEvidenceOfValidIds hv hn
  endpoint_owner := by
    intro endpoint
    have hcovered :
        endpoint.val ∈ List.range boundary.length ∨
          endpoint.val ∈ st.nodeIncidentIds := by
      simpa [ownerEndpointIds] using ho.owner_covered endpoint.val endpoint.isLt
    rcases hcovered with hboundary | hnode
    · rcases boundaryEvidenceOfPrefix_exists_of_boundary_id pref endpoint
          hboundary with
        ⟨boundaryIndex, hboundaryOwner⟩
      refine ⟨.boundary boundaryIndex, by simpa using hboundaryOwner, ?_⟩
      intro owner' howner'
      cases owner' with
      | boundary boundaryIndex' =>
          have hownerBoundary' :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex' =
                endpoint := by
            simpa using howner'
          have hsameEndpoint :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex' =
                (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex :=
            hownerBoundary'.trans hboundaryOwner.symm
          have hindex :
              boundaryIndex' = boundaryIndex :=
            (boundaryEvidenceOfPrefix pref).boundary_injective hsameEndpoint
          cases hindex
          rfl
      | constructor node slot =>
          have hownerConstructor' :
              (incidentOfValidIds hv node).get slot = endpoint := by
            simpa [incidenceEvidenceOfValidIds] using howner'
          have hsameEndpoint :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex =
                (incidentOfValidIds hv node).get slot :=
            hboundaryOwner.trans hownerConstructor'.symm
          exact False.elim
            (boundaryEvidenceOfPrefix_ne_incidentOfValidIds pref hv ho
              boundaryIndex node slot hsameEndpoint)
    · rcases incidentOfValidIds_exists_of_mem_nodeIncidentIds hv endpoint
          hnode with
        ⟨node, slot, hconstructorOwner⟩
      refine ⟨.constructor node slot, by
        simpa [incidenceEvidenceOfValidIds] using hconstructorOwner, ?_⟩
      intro owner' howner'
      cases owner' with
      | boundary boundaryIndex =>
          have hownerBoundary' :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex =
                endpoint := by
            simpa using howner'
          have hsameEndpoint :
              (boundaryEvidenceOfPrefix pref).boundaryPort boundaryIndex =
                (incidentOfValidIds hv node).get slot :=
            hownerBoundary'.trans hconstructorOwner.symm
          exact False.elim
            (boundaryEvidenceOfPrefix_ne_incidentOfValidIds pref hv ho
              boundaryIndex node slot hsameEndpoint)
      | constructor node' slot' =>
          have hownerConstructor' :
              (incidentOfValidIds hv node').get slot' = endpoint := by
            simpa [incidenceEvidenceOfValidIds] using howner'
          have hsameEndpoint :
              (incidentOfValidIds hv node').get slot' =
                (incidentOfValidIds hv node).get slot :=
            hownerConstructor'.trans hconstructorOwner.symm
          have hnodeEq :
              node' = node :=
            incidentOfValidIds_eq_node_eq hv ho hsameEndpoint
          cases hnodeEq
          have hslotEq :
              slot' = slot :=
            incidentOfValidIds_injective hv hn node hsameEndpoint
          cases hslotEq
          rfl

namespace PortHypergraphEvidence

def toPortHypergraph {st : RenderState Sig []} {boundary : List Sig.Port}
    (ev : PortHypergraphEvidence st boundary) :
    PortHypergraph Sig boundary where
  endpointCount := st.endpoints.length
  edgeCount := st.edges.length
  nodeCount := st.nodes.length
  endpointLabel := st.endpoints.get
  edgeLabel := fun edge => (st.edges.get edge).label
  endpointEdge := ev.edgeEvidence.endpointEdgeEvidence.endpointEdge
  endpoint_edge_label := ev.edgeEvidence.endpointEdgeEvidence.endpoint_edge_label
  edge_compatible := ev.edgeEvidence.edge_compatible
  edge_two_endpoints := ev.edgeEvidence.edge_two_endpoints
  boundaryPort := ev.boundaryEvidence.boundaryPort
  boundary_injective := ev.boundaryEvidence.boundary_injective
  boundary_label := ev.boundaryEvidence.boundary_label
  nodeLabel := fun node => (st.nodes.get node).label
  incident := ev.incidenceEvidence.incident
  incident_length := ev.incidenceEvidence.incident_length
  incident_injective := ev.incidenceEvidence.incident_injective
  incidence_label := ev.incidenceEvidence.incidence_label
  endpoint_owner := by
    intro endpoint
    rcases ev.endpoint_owner endpoint with ⟨owner, howner, huniq⟩
    cases owner with
    | boundary boundaryIndex =>
        refine ⟨.boundary boundaryIndex, by simpa using howner, ?_⟩
        intro owner' howner'
        cases owner' with
        | boundary boundaryIndex' =>
            exact huniq (.boundary boundaryIndex') (by simpa using howner')
        | constructor node slot =>
            exact huniq (.constructor node slot) (by simpa using howner')
    | constructor node slot =>
        refine ⟨.constructor node slot, by simpa using howner, ?_⟩
        intro owner' howner'
        cases owner' with
        | boundary boundaryIndex =>
            exact huniq (.boundary boundaryIndex) (by simpa using howner')
        | constructor node' slot' =>
            exact huniq (.constructor node' slot') (by simpa using howner')

end PortHypergraphEvidence

theorem rawReachesBoundary_to_portReachesBoundaryOfInvariants
    {st : RenderState Sig []} {boundary : List Sig.Port}
    (hv : st.ValidIds) (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    {id : Nat} (hbound : id < st.endpoints.length)
    (reach : st.RawReachesBoundary boundary.length id) :
    PortHypergraph.PortReachesBoundary
      (portHypergraphEvidenceOfInvariants hv hp hn pref ho).toPortHypergraph
      ⟨id, hbound⟩ := by
  let ev := portHypergraphEvidenceOfInvariants hv hp hn pref ho
  let G := ev.toPortHypergraph
  change PortHypergraph.PortReachesBoundary G ⟨id, hbound⟩
  induction reach with
  | boundary hboundary =>
      let boundaryIndex : Fin boundary.length :=
        ⟨_, List.mem_range.mp hboundary⟩
      have hendpoint :
          G.boundaryPort boundaryIndex = ⟨_, hbound⟩ := by
        apply Fin.ext
        rfl
      simpa [hendpoint] using
        (PortHypergraph.PortReachesBoundary.boundary
          (G := G) boundaryIndex)
  | throughEdgeLeft edge hmem _reach ih =>
      rcases list_exists_get_of_mem st.edges hmem with ⟨edgeIndex, hedgeEq⟩
      subst edge
      have hedgeMem : st.edges.get edgeIndex ∈ st.edges :=
        List.get_mem st.edges edgeIndex
      have hleftBound :=
        hv.edge_left_bound (st.edges.get edgeIndex) hedgeMem
      have hrightBound :=
        hv.edge_right_bound (st.edges.get edgeIndex) hedgeMem
      have hleftEdge :
          G.endpointEdge ⟨(st.edges.get edgeIndex).left, hleftBound⟩ =
            edgeIndex := by
        have h := endpointEdgeOfPartition_left hv hp edgeIndex
        simpa [G, ev, PortHypergraphEvidence.toPortHypergraph,
          portHypergraphEvidenceOfInvariants, edgeEvidenceOfPartition,
          endpointEdgeEvidenceOfPartition] using h
      have hrightEdge :
          G.endpointEdge ⟨(st.edges.get edgeIndex).right, hrightBound⟩ =
            edgeIndex := by
        have h := endpointEdgeOfPartition_right hv hp edgeIndex
        simpa [G, ev, PortHypergraphEvidence.toPortHypergraph,
          portHypergraphEvidenceOfInvariants, edgeEvidenceOfPartition,
          endpointEdgeEvidenceOfPartition] using h
      have hsame :
          G.endpointEdge ⟨(st.edges.get edgeIndex).left, hleftBound⟩ =
            G.endpointEdge ⟨(st.edges.get edgeIndex).right, hrightBound⟩ :=
        hleftEdge.trans hrightEdge.symm
      have hdiff :
          (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length) ≠
            ⟨(st.edges.get edgeIndex).right, hrightBound⟩ := by
        intro heq
        have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) heq
        have hne := edge_left_ne_right_of_partition hp edgeIndex
        exact hne hval
      have hreachRight :
          PortHypergraph.PortReachesBoundary G
            ⟨(st.edges.get edgeIndex).right, hrightBound⟩ :=
        PortHypergraph.PortReachesBoundary.throughEdge hsame hdiff
          (ih hleftBound)
      have htarget :
          (⟨(st.edges.get edgeIndex).right, hrightBound⟩ :
              Fin st.endpoints.length) =
            ⟨(st.edges.get edgeIndex).right, hbound⟩ := by
        apply Fin.ext
        rfl
      simpa [htarget] using hreachRight
  | throughEdgeRight edge hmem _reach ih =>
      rcases list_exists_get_of_mem st.edges hmem with ⟨edgeIndex, hedgeEq⟩
      subst edge
      have hedgeMem : st.edges.get edgeIndex ∈ st.edges :=
        List.get_mem st.edges edgeIndex
      have hleftBound :=
        hv.edge_left_bound (st.edges.get edgeIndex) hedgeMem
      have hrightBound :=
        hv.edge_right_bound (st.edges.get edgeIndex) hedgeMem
      have hleftEdge :
          G.endpointEdge ⟨(st.edges.get edgeIndex).left, hleftBound⟩ =
            edgeIndex := by
        have h := endpointEdgeOfPartition_left hv hp edgeIndex
        simpa [G, ev, PortHypergraphEvidence.toPortHypergraph,
          portHypergraphEvidenceOfInvariants, edgeEvidenceOfPartition,
          endpointEdgeEvidenceOfPartition] using h
      have hrightEdge :
          G.endpointEdge ⟨(st.edges.get edgeIndex).right, hrightBound⟩ =
            edgeIndex := by
        have h := endpointEdgeOfPartition_right hv hp edgeIndex
        simpa [G, ev, PortHypergraphEvidence.toPortHypergraph,
          portHypergraphEvidenceOfInvariants, edgeEvidenceOfPartition,
          endpointEdgeEvidenceOfPartition] using h
      have hsame :
          G.endpointEdge ⟨(st.edges.get edgeIndex).right, hrightBound⟩ =
            G.endpointEdge ⟨(st.edges.get edgeIndex).left, hleftBound⟩ :=
        hrightEdge.trans hleftEdge.symm
      have hdiff :
          (⟨(st.edges.get edgeIndex).right, hrightBound⟩ :
              Fin st.endpoints.length) ≠
            ⟨(st.edges.get edgeIndex).left, hleftBound⟩ := by
        intro heq
        have hval := congrArg (fun endpoint : Fin st.endpoints.length => endpoint.val) heq
        have hne := edge_left_ne_right_of_partition hp edgeIndex
        exact hne hval.symm
      have hreachLeft :
          PortHypergraph.PortReachesBoundary G
            ⟨(st.edges.get edgeIndex).left, hleftBound⟩ :=
        PortHypergraph.PortReachesBoundary.throughEdge hsame hdiff
          (ih hrightBound)
      have htarget :
          (⟨(st.edges.get edgeIndex).left, hleftBound⟩ :
              Fin st.endpoints.length) =
            ⟨(st.edges.get edgeIndex).left, hbound⟩ := by
        apply Fin.ext
        rfl
      simpa [htarget] using hreachLeft
  | throughConstructor node hmem fromSlot toSlot _reach ih =>
      rcases list_exists_get_of_mem st.nodes hmem with ⟨nodeIndex, hnodeEq⟩
      subst node
      have hnodeMem : st.nodes.get nodeIndex ∈ st.nodes :=
        List.get_mem st.nodes nodeIndex
      let fromSlot' : Fin (incidentOfValidIds hv nodeIndex).length :=
        Fin.cast (by simp [incidentOfValidIds]) fromSlot
      let toSlot' : Fin (incidentOfValidIds hv nodeIndex).length :=
        Fin.cast (by simp [incidentOfValidIds]) toSlot
      have hfromBound :=
        hv.node_incident_bound (st.nodes.get nodeIndex) hnodeMem fromSlot
      have htoBound :=
        hv.node_incident_bound (st.nodes.get nodeIndex) hnodeMem toSlot
      have hfrom :
          (G.incident nodeIndex).get fromSlot' =
            (⟨(st.nodes.get nodeIndex).incident.get fromSlot, hfromBound⟩ :
              Fin st.endpoints.length) := by
        apply Fin.ext
        simp [G, ev, PortHypergraphEvidence.toPortHypergraph,
          portHypergraphEvidenceOfInvariants, incidenceEvidenceOfValidIds,
          incidentOfValidIds, fromSlot']
      have hto :
          (G.incident nodeIndex).get toSlot' =
            (⟨(st.nodes.get nodeIndex).incident.get toSlot, htoBound⟩ :
              Fin st.endpoints.length) := by
        apply Fin.ext
        simp [G, ev, PortHypergraphEvidence.toPortHypergraph,
          portHypergraphEvidenceOfInvariants, incidenceEvidenceOfValidIds,
          incidentOfValidIds, toSlot']
      have hreachTo :
          PortHypergraph.PortReachesBoundary G
            (⟨(st.nodes.get nodeIndex).incident.get toSlot, htoBound⟩ :
              Fin st.endpoints.length) :=
        PortHypergraph.PortReachesBoundary.throughConstructor
          nodeIndex fromSlot' toSlot' hfrom hto (ih hfromBound)
      have htarget :
          (⟨(st.nodes.get nodeIndex).incident.get toSlot, htoBound⟩ :
              Fin st.endpoints.length) =
            ⟨(st.nodes.get nodeIndex).incident.get toSlot, hbound⟩ := by
        apply Fin.ext
        rfl
      simpa [htarget] using hreachTo

/-- Evidence that a completed render trace presents an open semantic graph. -/
structure OpenPortHypergraphEvidence
    (st : RenderState Sig []) (boundary : List Sig.Port) where
  graph : PortHypergraphEvidence st boundary
  allConstructorsReachBoundary :
    PortHypergraph.AllConstructorsReachBoundary graph.toPortHypergraph

namespace OpenPortHypergraphEvidence

def toOpenPortHypergraph {st : RenderState Sig []} {boundary : List Sig.Port}
    (ev : OpenPortHypergraphEvidence st boundary) :
    OpenPortHypergraph Sig boundary where
  raw := ev.graph.toPortHypergraph
  allConstructorsReachBoundary := ev.allConstructorsReachBoundary

end OpenPortHypergraphEvidence

end RenderState

namespace Diag

variable {Sig : Signature}

def renderTrace_endpointPrefixOfPrefix
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (pref : st.EndpointPrefix boundary) :
    (renderTrace d st).EndpointPrefix boundary :=
  pref.trans (renderTrace_endpointPrefix d st)

def renderTrace_graphEvidence
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary) :
    RenderState.PortHypergraphEvidence (renderTrace d st) boundary :=
  RenderState.portHypergraphEvidenceOfInvariants
    (renderTrace_validIds d st hv)
    (renderTrace_endpointPartition d st hv hp)
    (renderTrace_nodeIncidentNodup d st hn)
    (renderTrace_endpointPrefixOfPrefix d st pref)
    (renderTrace_ownerIdPartition d st boundary hv ho)

def renderTraceFromBoundary_graphEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.PortHypergraphEvidence (renderTraceFromBoundary d) boundary :=
  RenderState.portHypergraphEvidenceOfInvariants
    (renderTraceFromBoundary_validIds d)
    (renderTraceFromBoundary_endpointPartition d)
    (renderTraceFromBoundary_nodeIncidentNodup d)
    (renderTraceFromBoundary_endpointPrefix d)
    (renderTraceFromBoundary_ownerIdPartition d)

theorem renderTrace_allConstructorsReachBoundary
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    (hr : st.Reachability boundary) :
    PortHypergraph.AllConstructorsReachBoundary
      (renderTrace_graphEvidence d st hv hp hn pref ho).toPortHypergraph := by
  let final := renderTrace d st
  let finalHv : final.ValidIds := renderTrace_validIds d st hv
  let finalHp : final.EndpointPartition :=
    renderTrace_endpointPartition d st hv hp
  let finalHn : final.NodeIncidentNodup :=
    renderTrace_nodeIncidentNodup d st hn
  let finalPref : final.EndpointPrefix boundary :=
    renderTrace_endpointPrefixOfPrefix d st pref
  let finalHo : final.OwnerIdPartition boundary :=
    renderTrace_ownerIdPartition d st boundary hv ho
  let finalHr : final.Reachability boundary :=
    renderTrace_reachability d st hr
  let ev : RenderState.PortHypergraphEvidence final boundary :=
    RenderState.portHypergraphEvidenceOfInvariants
      finalHv finalHp finalHn finalPref finalHo
  let G := ev.toPortHypergraph
  change PortHypergraph.AllConstructorsReachBoundary G
  intro node
  have hnodeMem : final.nodes.get node ∈ final.nodes :=
    List.get_mem final.nodes node
  rcases finalHr.node_reaches (final.nodes.get node) hnodeMem with
    ⟨rawSlot, rawReach⟩
  let slot : Fin (G.incident node).length :=
    Fin.cast
      (by
        simp [G, ev, RenderState.PortHypergraphEvidence.toPortHypergraph,
          RenderState.portHypergraphEvidenceOfInvariants,
          RenderState.incidenceEvidenceOfValidIds,
          RenderState.incidentOfValidIds])
      rawSlot
  refine ⟨slot, ?_⟩
  have hrawBound :
      (final.nodes.get node).incident.get rawSlot < final.endpoints.length :=
    finalHv.node_incident_bound (final.nodes.get node) hnodeMem rawSlot
  have hrawReach :
      PortHypergraph.PortReachesBoundary G
        (⟨(final.nodes.get node).incident.get rawSlot, hrawBound⟩ :
          Fin final.endpoints.length) :=
    RenderState.rawReachesBoundary_to_portReachesBoundaryOfInvariants
      finalHv finalHp finalHn finalPref finalHo hrawBound rawReach
  have hendpoint :
      (G.incident node).get slot =
        (⟨(final.nodes.get node).incident.get rawSlot, hrawBound⟩ :
          Fin final.endpoints.length) := by
    apply Fin.ext
    simp [G, ev, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.incidenceEvidenceOfValidIds,
      RenderState.incidentOfValidIds, slot]
  exact hendpoint.symm ▸ hrawReach

theorem renderTraceFromBoundary_allConstructorsReachBoundary
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    PortHypergraph.AllConstructorsReachBoundary
      (renderTraceFromBoundary_graphEvidence d).toPortHypergraph := by
  simpa [renderTraceFromBoundary_graphEvidence, renderTraceFromBoundary,
    renderTrace_graphEvidence, renderTrace_endpointPrefixOfPrefix,
    RenderState.EndpointPrefix.trans] using
    renderTrace_allConstructorsReachBoundary d
      (RenderState.initial Sig boundary)
      (RenderState.initial_validIds boundary)
      (RenderState.initial_endpointPartition boundary)
      (RenderState.initial_nodeIncidentNodup boundary)
      { suffix := []
        endpoints_eq := by
          simp [RenderState.initial] }
      (RenderState.initial_ownerIdPartition boundary)
      (RenderState.initial_reachability boundary)

def renderTrace_openEvidence
    {frontier boundary : List Sig.Port} (d : Diag Sig frontier)
    (st : RenderState Sig frontier)
    (hv : st.ValidIds)
    (hp : st.EndpointPartition)
    (hn : st.NodeIncidentNodup)
    (pref : st.EndpointPrefix boundary)
    (ho : st.OwnerIdPartition boundary)
    (hr : st.Reachability boundary) :
    RenderState.OpenPortHypergraphEvidence (renderTrace d st) boundary where
  graph := renderTrace_graphEvidence d st hv hp hn pref ho
  allConstructorsReachBoundary :=
    renderTrace_allConstructorsReachBoundary d st hv hp hn pref ho hr

/--
Renderer validity: the trace produced from traversal syntax carries exactly
the endpoint, edge, boundary, ordered-constructor incidence, endpoint-owner, and
boundary-reachability evidence required to be an open `PortHypergraph`.
-/
def renderTraceFromBoundary_openEvidence
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderState.OpenPortHypergraphEvidence
      (renderTraceFromBoundary d) boundary where
  graph := renderTraceFromBoundary_graphEvidence d
  allConstructorsReachBoundary :=
    renderTraceFromBoundary_allConstructorsReachBoundary d

/-- Semantic renderer obtained from `renderTraceFromBoundary_openEvidence`. -/
def toOpenPortHypergraph
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    OpenPortHypergraph Sig boundary :=
  (renderTraceFromBoundary_openEvidence d).toOpenPortHypergraph

/--
Bridge support for the syntax round-trip: a rendered top-level `connect`
really makes the first ordered boundary endpoint an edge mate of the selected
later boundary endpoint in the semantic graph.
-/
theorem toOpenPortHypergraph_connect_boundary_edgeMate
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate)) :
    let d : Diag Sig (active :: frontier) := Diag.connect mate ok child
    let G := Diag.toOpenPortHypergraph d
    PortHypergraph.EdgeMate G.raw
      (G.raw.boundaryPort ⟨0, by simp⟩)
      (G.raw.boundaryPort ⟨mate.val + 1, by
        simp⟩) := by
  intro d G
  let st := renderTraceFromBoundary d
  let hp : st.EndpointPartition := renderTraceFromBoundary_endpointPartition d
  let restIds : List Nat := List.map Nat.succ (List.range frontier.length)
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := 0
      right :=
        restIds.get (Fin.cast (by
          have hids :
              (RenderState.initial Sig (active :: frontier)).frontierIds =
                0 :: restIds := by
            simp [RenderState.initial, restIds]
            exact List.range_succ_eq_map
          have hlen :=
            (RenderState.initial Sig (active :: frontier)).frontierIds_length
          rw [hids] at hlen
          exact (Nat.succ.inj hlen).symm) mate)
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hmem : edge ∈ st.edges := by
    simpa [d, st, renderTraceFromBoundary, RenderState.initial, edge] using
      renderTrace_connect_edge_mem mate ok child
        (RenderState.initial Sig (active :: frontier))
        (activeId := 0) (restIds := restIds)
        (by
          simp [RenderState.initial, restIds]
          exact List.range_succ_eq_map)
  rcases list_exists_get_of_mem st.edges hmem with ⟨edgeIndex, hedgeIndex⟩
  have hactiveVal :
      (G.raw.boundaryPort ⟨0, by simp⟩).val =
        (st.edges.get edgeIndex).left := by
    dsimp [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.boundaryEvidenceOfPrefix, edge] at *
    rw [hedgeIndex]
  have hmateVal :
      (G.raw.boundaryPort ⟨mate.val + 1, by
        simp⟩).val =
        (st.edges.get edgeIndex).right := by
    dsimp [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.boundaryEvidenceOfPrefix, edge] at *
    rw [hedgeIndex]
    simp [restIds]
  constructor
  · intro hsame
    have hval := congrArg (fun endpoint => endpoint.val) hsame
    have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
    exact hne (by
      calc
        (st.edges.get edgeIndex).left =
            (G.raw.boundaryPort ⟨0, by simp⟩).val := hactiveVal.symm
        _ = (G.raw.boundaryPort ⟨mate.val + 1, by
              simp⟩).val := hval
        _ = (st.edges.get edgeIndex).right := hmateVal)
  · have hleft :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (G.raw.boundaryPort ⟨0, by simp⟩) edgeIndex (Or.inl hactiveVal)
    have hright :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (G.raw.boundaryPort ⟨mate.val + 1, by
          simp⟩) edgeIndex (Or.inr hmateVal)
    simpa [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

/--
Bridge support for the syntax round-trip: a rendered top-level `bud` creates a
semantic constructor with the original label and entry position, and the first
ordered boundary endpoint is edge-mated to that constructor entry endpoint.
-/
theorem toOpenPortHypergraph_bud_boundary_entry_edgeMate
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry)) :
    let d : Diag Sig (active :: frontier) := Diag.bud node entry ok child
    let G := Diag.toOpenPortHypergraph d
    ∃ (nodeIndex : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident nodeIndex).length),
      G.raw.nodeLabel nodeIndex = node ∧
        slot.val = entry.val ∧
        PortHypergraph.EdgeMate G.raw
          (G.raw.boundaryPort ⟨0, by simp⟩)
          ((G.raw.incident nodeIndex).get slot) := by
  intro d G
  let st := renderTraceFromBoundary d
  let hv : st.ValidIds := renderTraceFromBoundary_validIds d
  let hp : st.EndpointPartition := renderTraceFromBoundary_endpointPartition d
  let nodeEndpoints :=
    freshNodeEndpoints (RenderState.initial Sig (active :: frontier)).nextEndpoint
      (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    Fin.cast (by simp [nodeEndpoints]) entry
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := 0
      right := nodeEndpoints.get entryIdx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  have hedgeMem : edge ∈ st.edges := by
    simpa [d, st, renderTraceFromBoundary, RenderState.initial, edge,
      nodeEndpoints, entryIdx] using
      renderTrace_bud_edge_mem node entry ok child
        (RenderState.initial Sig (active :: frontier))
        (activeId := 0)
        (restIds := List.map Nat.succ (List.range frontier.length))
        (by
          simp [RenderState.initial]
          exact List.range_succ_eq_map)
  have hnodeMem : renderNode ∈ st.nodes := by
    simpa [d, st, renderTraceFromBoundary, RenderState.initial, renderNode,
      nodeEndpoints] using
      renderTrace_bud_node_mem node entry ok child
        (RenderState.initial Sig (active :: frontier))
  rcases list_exists_get_of_mem st.edges hedgeMem with ⟨edgeIndex, hedgeIndex⟩
  rcases list_exists_get_of_mem st.nodes hnodeMem with ⟨nodeIndex, hnodeIndex⟩
  have hnodeLabel : G.raw.nodeLabel nodeIndex = node := by
    dsimp [G, Diag.toOpenPortHypergraph,
      RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
      renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
      RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants, renderNode,
      nodeEndpoints] at *
    rw [hnodeIndex]
  let slot : Fin (G.raw.incident nodeIndex).length :=
    Fin.cast (by
      calc
        Sig.arity node = Sig.arity (G.raw.nodeLabel nodeIndex) := by
          rw [hnodeLabel]
        _ = (G.raw.incident nodeIndex).length :=
          (G.raw.incident_length nodeIndex).symm) entry
  refine ⟨nodeIndex, slot, hnodeLabel, ?_, ?_⟩
  · simp [slot]
  · have hactiveVal :
        (G.raw.boundaryPort ⟨0, by simp⟩).val =
          (st.edges.get edgeIndex).left := by
      dsimp [G, Diag.toOpenPortHypergraph,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.boundaryEvidenceOfPrefix, edge] at *
      rw [hedgeIndex]
    have hincidentVal :
        ((G.raw.incident nodeIndex).get slot).val =
          (st.edges.get edgeIndex).right := by
      have hincidentList :
          (st.nodes.get nodeIndex).incident = nodeEndpoints := by
        simpa [renderNode] using congrArg RenderNode.incident hnodeIndex
      have hedgeRight :
          (st.edges.get edgeIndex).right = nodeEndpoints.get entryIdx := by
        simpa [edge] using congrArg RenderEdge.right hedgeIndex
      have hentryGet :
          (st.nodes.get nodeIndex).incident.get
              (Fin.cast (by
                rw [hincidentList]
                simp [nodeEndpoints]) entry) =
            nodeEndpoints.get entryIdx := by
        have hleftBound :
            entry.val < (st.nodes.get nodeIndex).incident.length := by
          rw [hincidentList]
          simp [nodeEndpoints]
        have hrightBound : entry.val < nodeEndpoints.length := by
          simp [nodeEndpoints]
        have hleftIdx :
            (Fin.cast (by
              rw [hincidentList]
              simp [nodeEndpoints]) entry :
                Fin (st.nodes.get nodeIndex).incident.length) =
              ⟨entry.val, hleftBound⟩ := by
          apply Fin.ext
          rfl
        have hrightIdx : entryIdx = ⟨entry.val, hrightBound⟩ := by
          apply Fin.ext
          rfl
        have hopt :
            (st.nodes.get nodeIndex).incident[entry.val]? =
              nodeEndpoints[entry.val]? := by
          rw [hincidentList]
        have hleftSome :
            (st.nodes.get nodeIndex).incident[entry.val]? =
              some ((st.nodes.get nodeIndex).incident.get
                ⟨entry.val, hleftBound⟩) :=
          List.getElem?_eq_getElem hleftBound
        have hrightSome :
            nodeEndpoints[entry.val]? =
              some (nodeEndpoints.get ⟨entry.val, hrightBound⟩) :=
          List.getElem?_eq_getElem hrightBound
        have hget :
            (st.nodes.get nodeIndex).incident.get ⟨entry.val, hleftBound⟩ =
              nodeEndpoints.get ⟨entry.val, hrightBound⟩ := by
          rw [hleftSome, hrightSome] at hopt
          injection hopt with hget
        rw [hleftIdx, hrightIdx]
        exact hget
      dsimp [G, Diag.toOpenPortHypergraph,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.incidenceEvidenceOfValidIds,
        RenderState.incidentOfValidIds, edge, slot, renderNode,
        nodeEndpoints, entryIdx]
      simpa [entryIdx] using hentryGet.trans hedgeRight.symm
    constructor
    · intro hsame
      have hval := congrArg (fun endpoint => endpoint.val) hsame
      have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
      exact hne (by
        calc
          (st.edges.get edgeIndex).left =
              (G.raw.boundaryPort ⟨0, by simp⟩).val := hactiveVal.symm
          _ = ((G.raw.incident nodeIndex).get slot).val := hval
          _ = (st.edges.get edgeIndex).right := hincidentVal)
    · have hleft :=
        RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
          (G.raw.boundaryPort ⟨0, by simp⟩) edgeIndex (Or.inl hactiveVal)
      have hright :=
        RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
          ((G.raw.incident nodeIndex).get slot) edgeIndex (Or.inr hincidentVal)
      simpa [G, Diag.toOpenPortHypergraph,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        renderTraceFromBoundary_openEvidence, renderTraceFromBoundary_graphEvidence,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.edgeEvidenceOfPartition,
        RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

end Diag

/--
Boundary-preserving isomorphism of typed finite representatives.  It relabels
endpoints, edges, and nodes, preserves the ordered boundary pointwise,
preserves endpoint/edge/node labels, preserves endpoint-to-edge incidence, and
preserves every ordered constructor-port incidence.
-/
structure PortHypergraphIso {Sig : Signature} {boundary : List Sig.Port}
    (G H : PortHypergraph Sig boundary) where
  endpointEquiv : Fin G.endpointCount ≃ᵢ Fin H.endpointCount
  edgeEquiv : Fin G.edgeCount ≃ᵢ Fin H.edgeCount
  nodeEquiv : Fin G.nodeCount ≃ᵢ Fin H.nodeCount
  boundary_preserved :
    ∀ b : Fin boundary.length,
      endpointEquiv.toFun (G.boundaryPort b) = H.boundaryPort b
  boundary_reflected :
    ∀ b : Fin boundary.length,
      endpointEquiv.invFun (H.boundaryPort b) = G.boundaryPort b
  endpoint_label_preserved :
    ∀ endpoint : Fin G.endpointCount,
      G.endpointLabel endpoint =
        H.endpointLabel (endpointEquiv.toFun endpoint)
  endpoint_label_reflected :
    ∀ endpoint : Fin H.endpointCount,
      H.endpointLabel endpoint =
        G.endpointLabel (endpointEquiv.invFun endpoint)
  edge_label_preserved :
    ∀ edge : Fin G.edgeCount,
      G.edgeLabel edge = H.edgeLabel (edgeEquiv.toFun edge)
  edge_label_reflected :
    ∀ edge : Fin H.edgeCount,
      H.edgeLabel edge = G.edgeLabel (edgeEquiv.invFun edge)
  endpoint_edge_preserved :
    ∀ endpoint : Fin G.endpointCount,
      H.endpointEdge (endpointEquiv.toFun endpoint) =
        edgeEquiv.toFun (G.endpointEdge endpoint)
  endpoint_edge_reflected :
    ∀ endpoint : Fin H.endpointCount,
      G.endpointEdge (endpointEquiv.invFun endpoint) =
        edgeEquiv.invFun (H.endpointEdge endpoint)
  node_label_preserved :
    ∀ node : Fin G.nodeCount,
      G.nodeLabel node = H.nodeLabel (nodeEquiv.toFun node)
  node_label_reflected :
    ∀ node : Fin H.nodeCount,
      H.nodeLabel node = G.nodeLabel (nodeEquiv.invFun node)
  incidence_preserved :
    ∀ node : Fin G.nodeCount,
      (G.incident node).map endpointEquiv.toFun =
        H.incident (nodeEquiv.toFun node)
  incidence_reflected :
    ∀ node : Fin H.nodeCount,
      (H.incident node).map endpointEquiv.invFun =
        G.incident (nodeEquiv.invFun node)

namespace PortHypergraphIso

variable {Sig : Signature} {boundary : List Sig.Port}

def refl (G : PortHypergraph Sig boundary) : PortHypergraphIso G G where
  endpointEquiv := Iso.refl (Fin G.endpointCount)
  edgeEquiv := Iso.refl (Fin G.edgeCount)
  nodeEquiv := Iso.refl (Fin G.nodeCount)
  boundary_preserved := by
    intro _
    rfl
  boundary_reflected := by
    intro _
    rfl
  endpoint_label_preserved := by
    intro _
    rfl
  endpoint_label_reflected := by
    intro _
    rfl
  edge_label_preserved := by
    intro _
    rfl
  edge_label_reflected := by
    intro _
    rfl
  endpoint_edge_preserved := by
    intro _
    rfl
  endpoint_edge_reflected := by
    intro _
    rfl
  node_label_preserved := by
    intro _
    rfl
  node_label_reflected := by
    intro _
    rfl
  incidence_preserved := by
    intro _
    simp [Iso.refl]
  incidence_reflected := by
    intro _
    simp [Iso.refl]

def symm {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) : PortHypergraphIso H G where
  endpointEquiv := Iso.symm e.endpointEquiv
  edgeEquiv := Iso.symm e.edgeEquiv
  nodeEquiv := Iso.symm e.nodeEquiv
  boundary_preserved := e.boundary_reflected
  boundary_reflected := e.boundary_preserved
  endpoint_label_preserved := e.endpoint_label_reflected
  endpoint_label_reflected := e.endpoint_label_preserved
  edge_label_preserved := e.edge_label_reflected
  edge_label_reflected := e.edge_label_preserved
  endpoint_edge_preserved := e.endpoint_edge_reflected
  endpoint_edge_reflected := e.endpoint_edge_preserved
  node_label_preserved := e.node_label_reflected
  node_label_reflected := e.node_label_preserved
  incidence_preserved := e.incidence_reflected
  incidence_reflected := e.incidence_preserved

def trans {G H K : PortHypergraph Sig boundary}
    (e₁ : PortHypergraphIso G H) (e₂ : PortHypergraphIso H K) :
    PortHypergraphIso G K where
  endpointEquiv := Iso.trans e₁.endpointEquiv e₂.endpointEquiv
  edgeEquiv := Iso.trans e₁.edgeEquiv e₂.edgeEquiv
  nodeEquiv := Iso.trans e₁.nodeEquiv e₂.nodeEquiv
  boundary_preserved := by
    intro b
    simp [Iso.trans, Function.comp, e₁.boundary_preserved b,
      e₂.boundary_preserved b]
  boundary_reflected := by
    intro b
    simp [Iso.trans, Function.comp, e₂.boundary_reflected b,
      e₁.boundary_reflected b]
  endpoint_label_preserved := by
    intro endpoint
    calc
      G.endpointLabel endpoint =
          H.endpointLabel (e₁.endpointEquiv.toFun endpoint) :=
        e₁.endpoint_label_preserved endpoint
      _ =
          K.endpointLabel
            (e₂.endpointEquiv.toFun (e₁.endpointEquiv.toFun endpoint)) :=
        e₂.endpoint_label_preserved (e₁.endpointEquiv.toFun endpoint)
  endpoint_label_reflected := by
    intro endpoint
    calc
      K.endpointLabel endpoint =
          H.endpointLabel (e₂.endpointEquiv.invFun endpoint) :=
        e₂.endpoint_label_reflected endpoint
      _ =
          G.endpointLabel
            (e₁.endpointEquiv.invFun (e₂.endpointEquiv.invFun endpoint)) :=
        e₁.endpoint_label_reflected (e₂.endpointEquiv.invFun endpoint)
  edge_label_preserved := by
    intro edge
    calc
      G.edgeLabel edge = H.edgeLabel (e₁.edgeEquiv.toFun edge) :=
        e₁.edge_label_preserved edge
      _ = K.edgeLabel (e₂.edgeEquiv.toFun (e₁.edgeEquiv.toFun edge)) :=
        e₂.edge_label_preserved (e₁.edgeEquiv.toFun edge)
  edge_label_reflected := by
    intro edge
    calc
      K.edgeLabel edge = H.edgeLabel (e₂.edgeEquiv.invFun edge) :=
        e₂.edge_label_reflected edge
      _ = G.edgeLabel (e₁.edgeEquiv.invFun (e₂.edgeEquiv.invFun edge)) :=
        e₁.edge_label_reflected (e₂.edgeEquiv.invFun edge)
  endpoint_edge_preserved := by
    intro endpoint
    calc
      K.endpointEdge
          (e₂.endpointEquiv.toFun (e₁.endpointEquiv.toFun endpoint)) =
          e₂.edgeEquiv.toFun
            (H.endpointEdge (e₁.endpointEquiv.toFun endpoint)) :=
        e₂.endpoint_edge_preserved (e₁.endpointEquiv.toFun endpoint)
      _ =
          e₂.edgeEquiv.toFun
            (e₁.edgeEquiv.toFun (G.endpointEdge endpoint)) := by
        rw [e₁.endpoint_edge_preserved endpoint]
  endpoint_edge_reflected := by
    intro endpoint
    calc
      G.endpointEdge
          (e₁.endpointEquiv.invFun (e₂.endpointEquiv.invFun endpoint)) =
          e₁.edgeEquiv.invFun
            (H.endpointEdge (e₂.endpointEquiv.invFun endpoint)) :=
        e₁.endpoint_edge_reflected (e₂.endpointEquiv.invFun endpoint)
      _ =
          e₁.edgeEquiv.invFun
            (e₂.edgeEquiv.invFun (K.endpointEdge endpoint)) := by
        rw [e₂.endpoint_edge_reflected endpoint]
  node_label_preserved := by
    intro node
    calc
      G.nodeLabel node = H.nodeLabel (e₁.nodeEquiv.toFun node) :=
        e₁.node_label_preserved node
      _ = K.nodeLabel (e₂.nodeEquiv.toFun (e₁.nodeEquiv.toFun node)) :=
        e₂.node_label_preserved (e₁.nodeEquiv.toFun node)
  node_label_reflected := by
    intro node
    calc
      K.nodeLabel node = H.nodeLabel (e₂.nodeEquiv.invFun node) :=
        e₂.node_label_reflected node
      _ = G.nodeLabel (e₁.nodeEquiv.invFun (e₂.nodeEquiv.invFun node)) :=
        e₁.node_label_reflected (e₂.nodeEquiv.invFun node)
  incidence_preserved := by
    intro node
    calc
      (G.incident node).map (Iso.trans e₁.endpointEquiv e₂.endpointEquiv).toFun =
          ((G.incident node).map e₁.endpointEquiv.toFun).map
            e₂.endpointEquiv.toFun := by
        simp [Iso.trans, List.map_map]
      _ = (H.incident (e₁.nodeEquiv.toFun node)).map
            e₂.endpointEquiv.toFun := by
        rw [e₁.incidence_preserved node]
      _ = K.incident (e₂.nodeEquiv.toFun (e₁.nodeEquiv.toFun node)) := by
        rw [e₂.incidence_preserved (e₁.nodeEquiv.toFun node)]
  incidence_reflected := by
    intro node
    calc
      (K.incident node).map (Iso.trans e₁.endpointEquiv e₂.endpointEquiv).invFun =
          ((K.incident node).map e₂.endpointEquiv.invFun).map
            e₁.endpointEquiv.invFun := by
        simp [Iso.trans, List.map_map]
      _ = (H.incident (e₂.nodeEquiv.invFun node)).map
            e₁.endpointEquiv.invFun := by
        rw [e₂.incidence_reflected node]
      _ = G.incident (e₁.nodeEquiv.invFun (e₂.nodeEquiv.invFun node)) := by
        rw [e₁.incidence_reflected (e₂.nodeEquiv.invFun node)]

theorem edgeMate_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    {endpoint mate : Fin G.endpointCount}
    (hmate : PortHypergraph.EdgeMate G endpoint mate) :
    PortHypergraph.EdgeMate H
      (e.endpointEquiv.toFun endpoint) (e.endpointEquiv.toFun mate) := by
  constructor
  · intro hsame
    have hpre :
        endpoint = mate := by
      have h := congrArg e.endpointEquiv.invFun hsame
      simpa using h
    exact hmate.1 hpre
  · rw [e.endpoint_edge_preserved endpoint,
      e.endpoint_edge_preserved mate, hmate.2]

theorem edgeMate_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    {endpoint mate : Fin H.endpointCount}
    (hmate : PortHypergraph.EdgeMate H endpoint mate) :
    PortHypergraph.EdgeMate G
      (e.endpointEquiv.invFun endpoint) (e.endpointEquiv.invFun mate) :=
  edgeMate_preserved (symm e) hmate

def incidenceSlotPreserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    Fin (H.incident (e.nodeEquiv.toFun node)).length :=
  Fin.cast
    (by
      have hlen := congrArg List.length (e.incidence_preserved node)
      simpa using hlen)
    slot

def incidenceSlotReflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount)
    (slot : Fin (H.incident node).length) :
    Fin (G.incident (e.nodeEquiv.invFun node)).length :=
  Fin.cast
    (by
      have hlen := congrArg List.length (e.incidence_reflected node)
      simpa using hlen)
    slot

theorem incidence_get_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    (H.incident (e.nodeEquiv.toFun node)).get
        (incidenceSlotPreserved e node slot) =
      e.endpointEquiv.toFun ((G.incident node).get slot) := by
  have hlist := congrArg (fun xs : List (Fin H.endpointCount) =>
      xs[slot.val]?) (e.incidence_preserved node)
  have hleftBound :
      slot.val < ((G.incident node).map e.endpointEquiv.toFun).length := by
    simp [slot.isLt]
  have hleftSome :
      ((G.incident node).map e.endpointEquiv.toFun)[slot.val]? =
        some (e.endpointEquiv.toFun ((G.incident node).get slot)) := by
    rw [List.getElem?_eq_getElem hleftBound]
    simp
  have hslotVal : (incidenceSlotPreserved e node slot).val = slot.val := rfl
  have hrightSome :
      (H.incident (e.nodeEquiv.toFun node))[slot.val]? =
        some ((H.incident (e.nodeEquiv.toFun node)).get
          (incidenceSlotPreserved e node slot)) := by
    rw [← hslotVal]
    exact List.getElem?_eq_getElem
      (incidenceSlotPreserved e node slot).isLt
  have hlist' :
      ((G.incident node).map e.endpointEquiv.toFun)[slot.val]? =
        (H.incident (e.nodeEquiv.toFun node))[slot.val]? := by
    simpa using hlist
  rw [hleftSome, hrightSome] at hlist'
  exact Option.some.inj hlist'.symm

theorem incidence_get_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount)
    (slot : Fin (H.incident node).length) :
    (G.incident (e.nodeEquiv.invFun node)).get
        (incidenceSlotReflected e node slot) =
      e.endpointEquiv.invFun ((H.incident node).get slot) := by
  have hlist := congrArg (fun xs : List (Fin G.endpointCount) =>
      xs[slot.val]?) (e.incidence_reflected node)
  have hleftBound :
      slot.val < ((H.incident node).map e.endpointEquiv.invFun).length := by
    simp [slot.isLt]
  have hleftSome :
      ((H.incident node).map e.endpointEquiv.invFun)[slot.val]? =
        some (e.endpointEquiv.invFun ((H.incident node).get slot)) := by
    rw [List.getElem?_eq_getElem hleftBound]
    simp
  have hslotVal : (incidenceSlotReflected e node slot).val = slot.val := rfl
  have hrightSome :
      (G.incident (e.nodeEquiv.invFun node))[slot.val]? =
        some ((G.incident (e.nodeEquiv.invFun node)).get
          (incidenceSlotReflected e node slot)) := by
    rw [← hslotVal]
    exact List.getElem?_eq_getElem
      (incidenceSlotReflected e node slot).isLt
  have hlist' :
      ((H.incident node).map e.endpointEquiv.invFun)[slot.val]? =
        (G.incident (e.nodeEquiv.invFun node))[slot.val]? := by
    simpa using hlist
  rw [hleftSome, hrightSome] at hlist'
  exact Option.some.inj hlist'.symm

theorem boundary_owner_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (boundaryIndex : Fin boundary.length) :
    PortHypergraph.endpointOwnerEndpoint H (.boundary boundaryIndex) =
      e.endpointEquiv.toFun
        (PortHypergraph.endpointOwnerEndpoint G (.boundary boundaryIndex)) := by
  simp [PortHypergraph.endpointOwnerEndpoint, e.boundary_preserved]

theorem constructor_owner_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin G.nodeCount)
    (slot : Fin (G.incident node).length) :
    PortHypergraph.endpointOwnerEndpoint H
        (.constructor (e.nodeEquiv.toFun node)
          (incidenceSlotPreserved e node slot)) =
      e.endpointEquiv.toFun
        (PortHypergraph.endpointOwnerEndpoint G (.constructor node slot)) := by
  simpa [PortHypergraph.endpointOwnerEndpoint] using
    incidence_get_preserved e node slot

theorem boundary_owner_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (boundaryIndex : Fin boundary.length) :
    PortHypergraph.endpointOwnerEndpoint G (.boundary boundaryIndex) =
      e.endpointEquiv.invFun
        (PortHypergraph.endpointOwnerEndpoint H (.boundary boundaryIndex)) := by
  simp [PortHypergraph.endpointOwnerEndpoint, e.boundary_reflected]

theorem constructor_owner_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) (node : Fin H.nodeCount)
    (slot : Fin (H.incident node).length) :
    PortHypergraph.endpointOwnerEndpoint G
        (.constructor (e.nodeEquiv.invFun node)
          (incidenceSlotReflected e node slot)) =
      e.endpointEquiv.invFun
        (PortHypergraph.endpointOwnerEndpoint H (.constructor node slot)) := by
  simpa [PortHypergraph.endpointOwnerEndpoint] using
    incidence_get_reflected e node slot

def endpointOwnerPreserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) :
    EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length) →
      EndpointOwner boundary.length H.nodeCount
        (fun node => (H.incident node).length)
  | .boundary boundaryIndex => .boundary boundaryIndex
  | .constructor node slot =>
      .constructor (e.nodeEquiv.toFun node)
        (incidenceSlotPreserved e node slot)

def endpointOwnerReflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) :
    EndpointOwner boundary.length H.nodeCount
        (fun node => (H.incident node).length) →
      EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length)
  | .boundary boundaryIndex => .boundary boundaryIndex
  | .constructor node slot =>
      .constructor (e.nodeEquiv.invFun node)
        (incidenceSlotReflected e node slot)

theorem endpointOwnerEndpoint_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    (owner : EndpointOwner boundary.length G.nodeCount
        (fun node => (G.incident node).length)) :
    PortHypergraph.endpointOwnerEndpoint H
        (endpointOwnerPreserved e owner) =
      e.endpointEquiv.toFun
        (PortHypergraph.endpointOwnerEndpoint G owner) := by
  cases owner with
  | boundary boundaryIndex =>
      exact boundary_owner_preserved e boundaryIndex
  | constructor node slot =>
      exact constructor_owner_preserved e node slot

theorem endpointOwnerEndpoint_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    (owner : EndpointOwner boundary.length H.nodeCount
        (fun node => (H.incident node).length)) :
    PortHypergraph.endpointOwnerEndpoint G
        (endpointOwnerReflected e owner) =
      e.endpointEquiv.invFun
        (PortHypergraph.endpointOwnerEndpoint H owner) := by
  cases owner with
  | boundary boundaryIndex =>
      exact boundary_owner_reflected e boundaryIndex
  | constructor node slot =>
      exact constructor_owner_reflected e node slot

def endpointOwnersOfPreserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin G.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf G endpoint) :
    PortHypergraph.endpointOwnersOf H (e.endpointEquiv.toFun endpoint) :=
  ⟨endpointOwnerPreserved e owner.1, by
    rw [endpointOwnerEndpoint_preserved e owner.1, owner.2]⟩

def endpointOwnersOfReflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin H.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf H endpoint) :
    PortHypergraph.endpointOwnersOf G (e.endpointEquiv.invFun endpoint) :=
  ⟨endpointOwnerReflected e owner.1, by
    rw [endpointOwnerEndpoint_reflected e owner.1, owner.2]⟩

theorem endpointOwnersOfPreserved_unique
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin G.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf G endpoint) :
    ∀ owner' : PortHypergraph.endpointOwnersOf H
        (e.endpointEquiv.toFun endpoint),
      owner' = endpointOwnersOfPreserved e owner := by
  rcases PortHypergraph.endpointOwnersOf_existsUnique H
      (e.endpointEquiv.toFun endpoint) with ⟨uniqueOwner, hunique⟩
  intro owner'
  exact (hunique owner').trans
    (hunique (endpointOwnersOfPreserved e owner)).symm

theorem endpointOwnersOfReflected_unique
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin H.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf H endpoint) :
    ∀ owner' : PortHypergraph.endpointOwnersOf G
        (e.endpointEquiv.invFun endpoint),
      owner' = endpointOwnersOfReflected e owner := by
  rcases PortHypergraph.endpointOwnersOf_existsUnique G
      (e.endpointEquiv.invFun endpoint) with ⟨uniqueOwner, hunique⟩
  intro owner'
  exact (hunique owner').trans
    (hunique (endpointOwnersOfReflected e owner)).symm

theorem endpointOwnersOf_unique_transport_preserved
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin G.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf G endpoint)
    (owner' : PortHypergraph.endpointOwnersOf H
        (e.endpointEquiv.toFun endpoint)) :
    owner' = endpointOwnersOfPreserved e owner :=
  endpointOwnersOfPreserved_unique e owner owner'

theorem endpointOwnersOf_unique_transport_reflected
    {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H) {endpoint : Fin H.endpointCount}
    (owner : PortHypergraph.endpointOwnersOf H endpoint)
    (owner' : PortHypergraph.endpointOwnersOf G
        (e.endpointEquiv.invFun endpoint)) :
    owner' = endpointOwnersOfReflected e owner :=
  endpointOwnersOfReflected_unique e owner owner'

theorem transport_contracts_preserved {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    {endpoint mate : Fin G.endpointCount}
    (hmate : PortHypergraph.EdgeMate G endpoint mate)
    (owner : PortHypergraph.endpointOwnersOf G endpoint) :
    PortHypergraph.EdgeMate H
        (e.endpointEquiv.toFun endpoint) (e.endpointEquiv.toFun mate) ∧
      PortHypergraph.endpointOwnerEndpoint H
          (endpointOwnersOfPreserved e owner).1 =
        e.endpointEquiv.toFun endpoint ∧
      (∀ owner' : PortHypergraph.endpointOwnersOf H
          (e.endpointEquiv.toFun endpoint),
        owner' = endpointOwnersOfPreserved e owner) := by
  exact ⟨edgeMate_preserved e hmate,
    (endpointOwnersOfPreserved e owner).2,
    endpointOwnersOfPreserved_unique e owner⟩

theorem transport_contracts_reflected {G H : PortHypergraph Sig boundary}
    (e : PortHypergraphIso G H)
    {endpoint mate : Fin H.endpointCount}
    (hmate : PortHypergraph.EdgeMate H endpoint mate)
    (owner : PortHypergraph.endpointOwnersOf H endpoint) :
    PortHypergraph.EdgeMate G
        (e.endpointEquiv.invFun endpoint) (e.endpointEquiv.invFun mate) ∧
      PortHypergraph.endpointOwnerEndpoint G
          (endpointOwnersOfReflected e owner).1 =
        e.endpointEquiv.invFun endpoint ∧
      (∀ owner' : PortHypergraph.endpointOwnersOf G
          (e.endpointEquiv.invFun endpoint),
        owner' = endpointOwnersOfReflected e owner) := by
  exact ⟨edgeMate_reflected e hmate,
    (endpointOwnersOfReflected e owner).2,
    endpointOwnersOfReflected_unique e owner⟩

end PortHypergraphIso

namespace OpenPortHypergraph

variable {Sig : Signature} {boundary : List Sig.Port}

/--
State for the boundary-rooted graph-to-syntax traversal.  The pending endpoint
list is ordered, and its labels are exactly the `Diag` frontier index.
-/
structure TraversalState (G : OpenPortHypergraph Sig boundary)
    (frontier : List Sig.Port) where
  pending : List (Fin G.raw.endpointCount)
  pending_labels : pending.map G.raw.endpointLabel = frontier
  seenNode : Fin G.raw.nodeCount → Prop
  processedEdge : Fin G.raw.edgeCount → Prop
  pending_unprocessed :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending → ¬ processedEdge (G.raw.endpointEdge endpoint)

namespace TraversalState

/--
The completeness invariant missing from the current traversal proof.  Every
unprocessed boundary endpoint, and every unprocessed endpoint of an already
seen constructor, must occur in the ordered pending frontier.
-/
def FrontierComplete {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : TraversalState G frontier) : Prop :=
  ∀ endpoint : Fin G.raw.endpointCount,
    ¬ st.processedEdge (G.raw.endpointEdge endpoint) →
      ∀ owner : EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length),
        PortHypergraph.endpointOwnerEndpoint G.raw owner = endpoint →
          match owner with
          | .boundary _ => endpoint ∈ st.pending
          | .constructor node _ => st.seenNode node → endpoint ∈ st.pending

end TraversalState

/--
Finite, data-carrying state for the owned graph-to-syntax search.

`TraversalState` is the proof-level invariant surface.  `SearchState` keeps the
same pending frontier together with finite lists of seen constructors and
processed edges, so a later traversal implementation can make constructor
choices as data and then project those choices back to the proof-level
invariants.
-/
structure SearchState (G : OpenPortHypergraph Sig boundary)
    (frontier : List Sig.Port) where
  pending : List (Fin G.raw.endpointCount)
  pending_labels : pending.map G.raw.endpointLabel = frontier
  pending_nodup : pending.Nodup
  seenNodes : List (Fin G.raw.nodeCount)
  processedEdges : List (Fin G.raw.edgeCount)
  processedEdges_nodup : processedEdges.Nodup
  pending_unprocessed :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending → G.raw.endpointEdge endpoint ∉ processedEdges
  pending_owner_seen :
    ∀ endpoint : Fin G.raw.endpointCount,
      endpoint ∈ pending →
        ∀ owner : EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length),
          PortHypergraph.endpointOwnerEndpoint G.raw owner = endpoint →
            match owner with
            | .boundary _ => True
            | .constructor node _ => node ∈ seenNodes
  unseen_incident_unprocessed :
    ∀ node : Fin G.raw.nodeCount,
      node ∉ seenNodes →
        ∀ slot : Fin (G.raw.incident node).length,
          G.raw.endpointEdge ((G.raw.incident node).get slot) ∉ processedEdges

namespace SearchState

private theorem cast_pending {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier) :
    (h ▸ st).pending = st.pending := by
  cases h
  rfl

private theorem cast_seenNodes {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier) :
    (h ▸ st).seenNodes = st.seenNodes := by
  cases h
  rfl

private theorem cast_processedEdges {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier) :
    (h ▸ st).processedEdges = st.processedEdges := by
  cases h
  rfl

private theorem nodePortsExcept_eq_of_val
    {nodeA nodeB : Sig.Node}
    (hnode : nodeA = nodeB)
    {entryA : Fin (Sig.arity nodeA)} {entryB : Fin (Sig.arity nodeB)}
    (hval : entryA.val = entryB.val) :
    Sig.nodePortsExcept nodeA entryA =
      Sig.nodePortsExcept nodeB entryB := by
  cases hnode
  have hentry : entryA = entryB := Fin.ext hval
  cases hentry
  rfl

def seenNode {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (node : Fin G.raw.nodeCount) : Prop :=
  node ∈ st.seenNodes

def processedEdge {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (edge : Fin G.raw.edgeCount) : Prop :=
  edge ∈ st.processedEdges

theorem processedEdges_length_le {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    st.processedEdges.length ≤ G.raw.edgeCount :=
  list_length_le_fin_of_nodup st.processedEdges st.processedEdges_nodup

def remainingEdges {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Nat :=
  G.raw.edgeCount - st.processedEdges.length

theorem processedEdges_length_lt_of_pending
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    (hactive : active ∈ st.pending) :
    st.processedEdges.length < G.raw.edgeCount := by
  have hfresh : G.raw.endpointEdge active ∉ st.processedEdges :=
    st.pending_unprocessed active hactive
  have hnodup :
      (G.raw.endpointEdge active :: st.processedEdges).Nodup := by
    constructor
    · intro edge hmem heq
      exact hfresh (by simpa [heq] using hmem)
    · exact st.processedEdges_nodup
  have hle :
      (G.raw.endpointEdge active :: st.processedEdges).length ≤
        G.raw.edgeCount :=
    list_length_le_fin_of_nodup
      (G.raw.endpointEdge active :: st.processedEdges) hnodup
  have hsucc :
      st.processedEdges.length + 1 ≤ G.raw.edgeCount := by
    simpa using hle
  exact Nat.lt_of_succ_le hsucc

def toTraversalState {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) :
    TraversalState G frontier where
  pending := st.pending
  pending_labels := st.pending_labels
  seenNode := st.seenNode
  processedEdge := st.processedEdge
  pending_unprocessed := by
    intro endpoint hpending hprocessed
    exact st.pending_unprocessed endpoint hpending hprocessed

/-- Proof-level frontier completeness for a finite search state. -/
def FrontierComplete {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Prop :=
  st.toTraversalState.FrontierComplete

/-- Frontier completeness transports across a cast of the frontier index. -/
theorem frontierComplete_cast {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier)
    (hc : st.FrontierComplete) :
    (h ▸ st).FrontierComplete := by
  cases h
  exact hc

/-- Initial finite search state: the ordered boundary endpoints are pending. -/
def initial (G : OpenPortHypergraph Sig boundary) : SearchState G boundary where
  pending := List.ofFn G.raw.boundaryPort
  pending_labels := by
    apply List.ext_getElem
    · simp [List.length_ofFn]
    · intro i hleft hright
      rw [List.getElem_map]
      rw [List.getElem_ofFn]
      exact G.raw.boundary_label ⟨i, hright⟩
  pending_nodup :=
    list_nodup_ofFn_injective G.raw.boundaryPort G.raw.boundary_injective
  seenNodes := []
  processedEdges := []
  processedEdges_nodup := by
    simp
  pending_unprocessed := by
    intro _endpoint _hpending
    simp
  pending_owner_seen := by
    intro endpoint hpending owner howner
    rw [List.mem_ofFn] at hpending
    rcases hpending with ⟨boundaryIndex, hboundary⟩
    cases owner with
    | boundary _ =>
        trivial
    | constructor node slot =>
        have hboundaryOwner :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.boundary boundaryIndex) = endpoint := by
          exact hboundary
        have hconstructorOwner :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = endpoint := howner
        rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
        have hboundaryEq :
            (.boundary boundaryIndex :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) = owner₀ := by
          apply huniq
          simpa [PortHypergraph.endpointOwnerEndpoint] using hboundaryOwner
        have hconstructorEq :
            (.constructor node slot :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) = owner₀ := by
          apply huniq
          simpa [PortHypergraph.endpointOwnerEndpoint] using hconstructorOwner
        have himpossible :
            (.constructor node slot :
              EndpointOwner boundary.length G.raw.nodeCount
                (fun node => (G.raw.incident node).length)) =
              .boundary boundaryIndex := by
          exact hconstructorEq.trans hboundaryEq.symm
        cases himpossible
  unseen_incident_unprocessed := by
    intro _node _hunseen _slot
    simp

theorem initial_frontierComplete (G : OpenPortHypergraph Sig boundary) :
    (initial G).FrontierComplete := by
  intro endpoint _hunprocessed owner howner
  cases owner with
  | boundary boundaryIndex =>
      have hownerEndpoint :
          G.raw.boundaryPort boundaryIndex = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      have hmem :
          G.raw.boundaryPort boundaryIndex ∈ List.ofFn G.raw.boundaryPort :=
        (List.mem_ofFn).mpr ⟨boundaryIndex, rfl⟩
      rw [hownerEndpoint] at hmem
      simpa [FrontierComplete, toTraversalState, initial] using hmem
  | constructor node _slot =>
      intro hseen
      simp [toTraversalState, initial, seenNode] at hseen

/--
Correspondence between a renderer prefix and an executable search state over
the final rendered graph.  Pending endpoints are exactly the renderer frontier,
processed edges are exactly the rendered edge prefix, and seen constructors are
exactly the rendered node prefix.
-/
structure RenderPrefixRelated
    {frontier : List Sig.Port}
    {final : RenderState Sig []}
    (ev : RenderState.OpenPortHypergraphEvidence final boundary)
    (rst : RenderState Sig frontier)
    (sst : SearchState ev.toOpenPortHypergraph frontier) : Prop where
  pending_vals :
    sst.pending.map (fun endpoint => endpoint.val) = rst.frontierIds
  processed_prefix :
    ∀ edge : Fin ev.toOpenPortHypergraph.raw.edgeCount,
      edge ∈ sst.processedEdges ↔ edge.val < rst.edges.length
  seen_prefix :
    ∀ node : Fin ev.toOpenPortHypergraph.raw.nodeCount,
      node ∈ sst.seenNodes ↔ node.val < rst.nodes.length

theorem RenderPrefixRelated.pending_cons_values
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: frontier)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    {activeId : Nat} {restIds : List Nat}
    (hids : rst.frontierIds = activeId :: restIds) :
    active.val = activeId ∧ rest.map (fun endpoint => endpoint.val) = restIds := by
  have hvals :
      (active :: rest).map (fun endpoint => endpoint.val) =
        activeId :: restIds := by
    rw [← hpending, hrel.pending_vals, hids]
  simpa using hvals

theorem initial_renderPrefixRelated
    {boundary : List Sig.Port} (d : Diag Sig boundary) :
    RenderPrefixRelated
      (Diag.renderTraceFromBoundary_openEvidence d)
      (RenderState.initial Sig boundary)
      (initial (Diag.toOpenPortHypergraph d)) where
  pending_vals := by
    apply List.ext_getElem
    · simp [initial, RenderState.initial]
    · intro i _hleft hright
      dsimp [initial, RenderState.initial, Diag.toOpenPortHypergraph,
        Diag.renderTraceFromBoundary_openEvidence,
        Diag.renderTraceFromBoundary_graphEvidence,
        RenderState.OpenPortHypergraphEvidence.toOpenPortHypergraph,
        RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.boundaryEvidenceOfPrefix]
      simp
  processed_prefix := by
    intro edge
    simp [initial, RenderState.initial]
  seen_prefix := by
    intro node
    simp [initial, RenderState.initial]

/--
State correspondence for two first-pending traversals over isomorphic graph
representatives.  The frontier labels are already the shared type index; this
relation records the stronger endpoint/node/edge correspondence needed for
traversal-invariance proofs.
-/
structure IsoRelated {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    {frontier : List Sig.Port}
    (left : SearchState G frontier) (right : SearchState H frontier) : Prop where
  pending_eq :
    right.pending = left.pending.map e.endpointEquiv.toFun
  seenNodes_eq :
    right.seenNodes = left.seenNodes.map e.nodeEquiv.toFun
  processedEdges_eq :
    right.processedEdges = left.processedEdges.map e.edgeEquiv.toFun

theorem initial_isoRelated {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw) :
    IsoRelated e (initial G) (initial H) where
  pending_eq := by
    apply List.ext_getElem
    · simp [initial]
    · intro i hleft hright
      simp [initial, e.boundary_preserved]
  seenNodes_eq := by
    simp [initial]
  processedEdges_eq := by
    simp [initial]

theorem IsoRelated.pending_cons {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hleft : left.pending = active :: rest) :
    right.pending =
      e.endpointEquiv.toFun active :: rest.map e.endpointEquiv.toFun := by
  rw [hr.pending_eq, hleft]
  rfl

theorem IsoRelated.pending_mem_preserved {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {endpoint : Fin G.raw.endpointCount}
    (hmem : endpoint ∈ left.pending) :
    e.endpointEquiv.toFun endpoint ∈ right.pending := by
  rw [hr.pending_eq]
  exact List.mem_map.mpr ⟨endpoint, hmem, rfl⟩

theorem IsoRelated.pending_mem_reflected {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {endpoint : Fin H.raw.endpointCount}
    (hmem : endpoint ∈ right.pending) :
    e.endpointEquiv.invFun endpoint ∈ left.pending := by
  rw [hr.pending_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨endpoint', hendpoint', heq⟩
  have hpre : e.endpointEquiv.invFun endpoint = endpoint' := by
    rw [← heq]
    simp
  simpa [hpre] using hendpoint'

theorem IsoRelated.seen_mem_preserved {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {node : Fin G.raw.nodeCount}
    (hmem : node ∈ left.seenNodes) :
    e.nodeEquiv.toFun node ∈ right.seenNodes := by
  rw [hr.seenNodes_eq]
  exact List.mem_map.mpr ⟨node, hmem, rfl⟩

theorem IsoRelated.seen_mem_reflected {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {node : Fin H.raw.nodeCount}
    (hmem : node ∈ right.seenNodes) :
    e.nodeEquiv.invFun node ∈ left.seenNodes := by
  rw [hr.seenNodes_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨node', hnode', heq⟩
  have hpre : e.nodeEquiv.invFun node = node' := by
    rw [← heq]
    simp
  simpa [hpre] using hnode'

theorem IsoRelated.processed_mem_preserved
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {edge : Fin G.raw.edgeCount}
    (hmem : edge ∈ left.processedEdges) :
    e.edgeEquiv.toFun edge ∈ right.processedEdges := by
  rw [hr.processedEdges_eq]
  exact List.mem_map.mpr ⟨edge, hmem, rfl⟩

theorem IsoRelated.processed_mem_reflected
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {edge : Fin H.raw.edgeCount}
    (hmem : edge ∈ right.processedEdges) :
    e.edgeEquiv.invFun edge ∈ left.processedEdges := by
  rw [hr.processedEdges_eq] at hmem
  rcases List.mem_map.mp hmem with ⟨edge', hedge', heq⟩
  have hpre : e.edgeEquiv.invFun edge = edge' := by
    rw [← heq]
    simp
  simpa [hpre] using hedge'

theorem IsoRelated.transport_contracts
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {frontier : List Sig.Port}
    {left : SearchState G frontier} {right : SearchState H frontier}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hleft : left.pending = active :: rest)
    {leftEndpoint : Fin G.raw.endpointCount}
    {rightEndpoint : Fin H.raw.endpointCount}
    (hleftPending : leftEndpoint ∈ left.pending)
    (hrightPending : rightEndpoint ∈ right.pending)
    {leftNode : Fin G.raw.nodeCount}
    {rightNode : Fin H.raw.nodeCount}
    (hleftSeen : leftNode ∈ left.seenNodes)
    (hrightSeen : rightNode ∈ right.seenNodes)
    {leftEdge : Fin G.raw.edgeCount}
    {rightEdge : Fin H.raw.edgeCount}
    (hleftProcessed : leftEdge ∈ left.processedEdges)
    (hrightProcessed : rightEdge ∈ right.processedEdges) :
    right.pending =
        e.endpointEquiv.toFun active ::
          rest.map e.endpointEquiv.toFun ∧
      e.endpointEquiv.toFun leftEndpoint ∈ right.pending ∧
      e.endpointEquiv.invFun rightEndpoint ∈ left.pending ∧
      e.nodeEquiv.toFun leftNode ∈ right.seenNodes ∧
      e.nodeEquiv.invFun rightNode ∈ left.seenNodes ∧
      e.edgeEquiv.toFun leftEdge ∈ right.processedEdges ∧
      e.edgeEquiv.invFun rightEdge ∈ left.processedEdges := by
  exact ⟨hr.pending_cons hleft,
    hr.pending_mem_preserved hleftPending,
    hr.pending_mem_reflected hrightPending,
    hr.seen_mem_preserved hleftSeen,
    hr.seen_mem_reflected hrightSeen,
    hr.processed_mem_preserved hleftProcessed,
    hr.processed_mem_reflected hrightProcessed⟩

theorem pending_cons_nodup {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    (active :: rest).Nodup := by
  simpa [hpending] using st.pending_nodup

theorem active_not_mem_rest {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    active ∉ rest := by
  have hnodup := st.pending_cons_nodup hpending
  have hsplit : ¬ active ∈ rest ∧ rest.Nodup := by
    simpa using hnodup
  exact hsplit.1

theorem rest_nodup {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    rest.Nodup := by
  have hnodup := st.pending_cons_nodup hpending
  have hsplit : ¬ active ∈ rest ∧ rest.Nodup := by
    simpa using hnodup
  exact hsplit.2

theorem pending_labels_cons {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    G.raw.endpointLabel active = activeLabel ∧
      rest.map G.raw.endpointLabel = restLabels := by
  have hlabels :
      (active :: rest).map G.raw.endpointLabel =
        activeLabel :: restLabels := by
    simpa [hpending] using st.pending_labels
  simpa using hlabels

theorem active_label_eq {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    G.raw.endpointLabel active = activeLabel :=
  (st.pending_labels_cons hpending).1

theorem rest_labels_eq {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest) :
    rest.map G.raw.endpointLabel = restLabels :=
  (st.pending_labels_cons hpending).2

def restLabelIndex {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length) : Fin restLabels.length :=
  let hrest := st.rest_labels_eq hpending
  Fin.cast (by
    rw [← hrest]
    simp) mate

theorem restLabelIndex_get {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length) :
    restLabels.get (st.restLabelIndex hpending mate) =
      G.raw.endpointLabel (rest.get mate) := by
  have hrest := st.rest_labels_eq hpending
  cases hrest
  simp [restLabelIndex]

theorem IsoRelated.restLabelIndex {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length) :
    right.restLabelIndex (hr.pending_cons hpending) (Fin.cast (by simp) mate) =
      left.restLabelIndex hpending mate := by
  apply Fin.ext
  rfl

theorem constructor_seen_of_pending {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    (st : SearchState G frontier)
    {endpoint : Fin G.raw.endpointCount}
    (hpending : endpoint ∈ st.pending)
    {node : Fin G.raw.nodeCount}
    {slot : Fin (G.raw.incident node).length}
    (howner :
      PortHypergraph.endpointOwnerEndpoint G.raw (.constructor node slot) =
        endpoint) :
    node ∈ st.seenNodes :=
  st.pending_owner_seen endpoint hpending (.constructor node slot) howner

end SearchState

/--
The local step condition needed by the first-pending traversal.  For the
active endpoint and the remaining ordered pending endpoints, the edge mate must
either already be in the remaining pending list, giving a `connect`, or be an
ordered port of an unseen constructor, giving a `bud`.
-/
def FirstPendingStepReady (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) : Prop :=
  (∃ mate : Fin rest.length,
    PortHypergraph.EdgeMate G.raw active (rest.get mate)) ∨
  (∃ (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length),
    PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot) ∧
      ¬ seenNode node)

/--
Data for one first-pending traversal step.  This is the constructor-level
choice object that `Diag` construction needs: either the active endpoint
connects to a later pending endpoint, or it enters an unseen constructor at an
ordered slot.
-/
inductive FirstPendingStep (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) : Type where
  | connect
      (mate : Fin rest.length)
      (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
      FirstPendingStep G seenNode active rest
  | bud
      (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length)
      (hmate :
        PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (unseen : ¬ seenNode node) :
      FirstPendingStep G seenNode active rest

namespace FirstPendingStep

theorem ready {G : OpenPortHypergraph Sig boundary}
    {seenNode : Fin G.raw.nodeCount → Prop}
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (step : FirstPendingStep G seenNode active rest) :
    FirstPendingStepReady G seenNode active rest := by
  cases step with
  | connect mate hmate =>
      exact Or.inl ⟨mate, hmate⟩
  | bud node slot hmate unseen =>
      exact Or.inr ⟨node, slot, hmate, unseen⟩

end FirstPendingStep

namespace SearchState

theorem connect_compatible {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    Sig.compatible activeLabel
      (restLabels.get (st.restLabelIndex hpending mate)) := by
  have hcompat := PortHypergraph.edgeMate_compatible G.raw hmate
  have hactive := st.active_label_eq hpending
  have hmateLabel := st.restLabelIndex_get hpending mate
  rw [hactive] at hcompat
  rw [← hmateLabel] at hcompat
  exact hcompat

def budEntry {G : OpenPortHypergraph Sig boundary}
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length) :
    Fin (Sig.arity (G.raw.nodeLabel node)) :=
  Fin.cast (G.raw.incident_length node) slot

theorem budEntry_val_preserved {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length) :
    (budEntry (G := H) (e.nodeEquiv.toFun node)
        (PortHypergraphIso.incidenceSlotPreserved e node slot)).val =
      (budEntry (G := G) node slot).val := by
  simp [budEntry, PortHypergraphIso.incidenceSlotPreserved]

theorem bud_compatible {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot)) :
    Sig.compatible activeLabel
      (Sig.port (G.raw.nodeLabel node) (budEntry node slot)) := by
  have hcompat := PortHypergraph.edgeMate_compatible G.raw hmate
  have hactive := st.active_label_eq hpending
  have hslot := G.raw.incidence_label node slot
  rw [hactive] at hcompat
  rw [hslot] at hcompat
  exact hcompat

def connectChild {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    SearchState G (eraseFin restLabels (st.restLabelIndex hpending mate)) where
  pending := eraseFin rest mate
  pending_labels := by
    calc
      (eraseFin rest mate).map G.raw.endpointLabel =
          eraseFin (rest.map G.raw.endpointLabel) (Fin.cast (by simp) mate) :=
        map_eraseFin G.raw.endpointLabel rest mate
      _ = eraseFin restLabels (st.restLabelIndex hpending mate) := by
        have hrest := st.rest_labels_eq hpending
        cases hrest
        simp [restLabelIndex]
  pending_nodup :=
    nodup_eraseFin rest mate (st.rest_nodup hpending)
  seenNodes := st.seenNodes
  processedEdges := G.raw.endpointEdge active :: st.processedEdges
  processedEdges_nodup := by
    have hactivePending : active ∈ st.pending := by
      rw [hpending]
      simp
    have hfresh : G.raw.endpointEdge active ∉ st.processedEdges :=
      st.pending_unprocessed active hactivePending
    constructor
    · intro edge hmem heq
      exact hfresh (by simpa [heq] using hmem)
    · exact st.processedEdges_nodup
  pending_unprocessed := by
    intro endpoint hmem hprocessed
    have hrestMem : endpoint ∈ rest :=
      mem_of_mem_eraseFin rest mate hmem
    have hstPending : endpoint ∈ st.pending := by
      rw [hpending]
      right
      exact hrestMem
    simp at hprocessed
    rcases hprocessed with hnew | hold
    · have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        exact st.active_not_mem_rest hpending (by
          simpa [hactiveEndpoint] using hrestMem)
      have hendpointMate : endpoint = rest.get mate := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : rest.get mate = uniqueMate :=
          huniq (rest.get mate) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnew.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hmateNotMem :
          rest.get mate ∉ eraseFin rest mate :=
        get_not_mem_eraseFin_of_nodup rest mate (st.rest_nodup hpending)
      exact hmateNotMem (by simpa [hendpointMate] using hmem)
    · exact st.pending_unprocessed endpoint hstPending hold
  pending_owner_seen := by
    intro endpoint hmem owner howner
    have hrestMem : endpoint ∈ rest :=
      mem_of_mem_eraseFin rest mate hmem
    have hstPending : endpoint ∈ st.pending := by
      rw [hpending]
      right
      exact hrestMem
    exact st.pending_owner_seen endpoint hstPending owner howner
  unseen_incident_unprocessed := by
    intro node hunseen slot hprocessed
    simp at hprocessed
    rcases hprocessed with hnew | hold
    · let endpoint := (G.raw.incident node).get slot
      have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        have hactivePending : active ∈ st.pending := by
          rw [hpending]
          simp
        have hownerActive :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = active := by
          change (G.raw.incident node).get slot = active
          exact hactiveEndpoint.symm
        have hseen : node ∈ st.seenNodes :=
          st.constructor_seen_of_pending hactivePending hownerActive
        exact hunseen hseen
      have hendpointMate :
          endpoint = rest.get mate := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : rest.get mate = uniqueMate :=
          huniq (rest.get mate) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnew.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hmatePending : rest.get mate ∈ st.pending := by
        rw [hpending]
        right
        exact List.get_mem rest mate
      have hownerMate :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = rest.get mate := by
        change (G.raw.incident node).get slot = rest.get mate
        exact hendpointMate
      have hseen : node ∈ st.seenNodes :=
        st.constructor_seen_of_pending hmatePending hownerMate
      exact hunseen hseen
    · exact st.unseen_incident_unprocessed node hunseen slot hold

theorem connectChild_frontierComplete {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (hcomplete : st.FrontierComplete) :
    (st.connectChild hpending mate hmate).FrontierComplete := by
  intro endpoint hunprocessed owner howner
  have hchildUnprocessed :
      G.raw.endpointEdge endpoint ∉
        G.raw.endpointEdge active :: st.processedEdges := by
    simpa [FrontierComplete, toTraversalState, connectChild, processedEdge]
      using hunprocessed
  have hnotActiveEdge :
      G.raw.endpointEdge endpoint ≠ G.raw.endpointEdge active := by
    intro hedge
    exact hchildUnprocessed (by simp [hedge])
  have holdUnprocessed :
      G.raw.endpointEdge endpoint ∉ st.processedEdges := by
    intro hold
    exact hchildUnprocessed (by simp [hold])
  have old_pending_to_child
      (holdPending : endpoint ∈ st.pending) :
      endpoint ∈ eraseFin rest mate := by
    have hrest : endpoint ∈ rest := by
      rw [hpending] at holdPending
      exact list_mem_tail_of_mem_cons_ne holdPending (by
        intro hactiveEndpoint
        exact hnotActiveEdge (by
          rw [← hactiveEndpoint]))
    have hnotMate : endpoint ≠ rest.get mate := by
      intro hendpointMate
      exact hnotActiveEdge (by
        rw [hendpointMate]
        exact hmate.2.symm)
    exact mem_eraseFin_of_mem_ne_get rest mate hrest hnotMate
  cases owner with
  | boundary boundaryIndex =>
      have holdPending :
          endpoint ∈ st.pending :=
        hcomplete endpoint holdUnprocessed (.boundary boundaryIndex) howner
      simpa [FrontierComplete, toTraversalState, connectChild]
        using old_pending_to_child holdPending
  | constructor node slot =>
      intro hseen
      have holdPending :
          endpoint ∈ st.pending :=
        hcomplete endpoint holdUnprocessed (.constructor node slot) howner hseen
      simpa [FrontierComplete, toTraversalState, connectChild, seenNode]
        using old_pending_to_child holdPending

def budChild {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    SearchState G
      (restLabels ++
        Sig.nodePortsExcept (G.raw.nodeLabel node) (budEntry node slot)) where
  pending := rest ++ eraseFin (G.raw.incident node) slot
  pending_labels := by
    calc
      (rest ++ eraseFin (G.raw.incident node) slot).map
          G.raw.endpointLabel =
          rest.map G.raw.endpointLabel ++
            (eraseFin (G.raw.incident node) slot).map G.raw.endpointLabel := by
        simp
      _ = restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node) (budEntry node slot) := by
        rw [st.rest_labels_eq hpending,
          G.raw.incident_labels_except node slot]
        rfl
  pending_nodup := by
    apply nodup_append_of_nodup_disjoint
    · exact st.rest_nodup hpending
    · exact nodup_eraseFin (G.raw.incident node) slot
        (G.raw.incident_nodup node)
    · intro endpoint hrest hnew
      have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnew
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      have howner :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot') = endpoint := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using hslot'
      have hseen : node ∈ st.seenNodes :=
        st.constructor_seen_of_pending hstPending howner
      exact hunseen hseen
  seenNodes := node :: st.seenNodes
  processedEdges := G.raw.endpointEdge active :: st.processedEdges
  processedEdges_nodup := by
    have hactivePending : active ∈ st.pending := by
      rw [hpending]
      simp
    have hfresh : G.raw.endpointEdge active ∉ st.processedEdges :=
      st.pending_unprocessed active hactivePending
    constructor
    · intro edge hmem heq
      exact hfresh (by simpa [heq] using hmem)
    · exact st.processedEdges_nodup
  pending_unprocessed := by
    intro endpoint hmem hprocessed
    simp at hmem
    simp at hprocessed
    rcases hmem with hrest | hnewEndpoint
    · have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      rcases hprocessed with hnewProcessed | hold
      · have hactiveNe : active ≠ endpoint := by
          intro hactiveEndpoint
          exact st.active_not_mem_rest hpending (by
            simpa [hactiveEndpoint] using hrest)
        have hendpointMate :
            endpoint = (G.raw.incident node).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw active with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
            huniq ((G.raw.incident node).get slot) hmate
          have hendpointEq : endpoint = uniqueMate :=
            huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
          exact hendpointEq.trans hmateEq.symm
        have hseen : node ∈ st.seenNodes :=
          st.constructor_seen_of_pending hstPending (by
            change (G.raw.incident node).get slot = endpoint
            exact hendpointMate.symm)
        exact hunseen hseen
      · exact st.pending_unprocessed endpoint hstPending hold
    · have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnewEndpoint
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      rcases hprocessed with hnewProcessed | hold
      · have hactiveNe : active ≠ endpoint := by
          intro hactiveEndpoint
          have hactivePending : active ∈ st.pending := by
            rw [hpending]
            simp
          have hseen : node ∈ st.seenNodes :=
            st.constructor_seen_of_pending hactivePending (by
              change (G.raw.incident node).get slot' = active
              exact hslot'.trans hactiveEndpoint.symm)
          exact hunseen hseen
        have hendpointEntry :
            endpoint = (G.raw.incident node).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw active with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
            huniq ((G.raw.incident node).get slot) hmate
          have hendpointEq : endpoint = uniqueMate :=
            huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
          exact hendpointEq.trans hmateEq.symm
        have hentryNotMem :
            (G.raw.incident node).get slot ∉
              eraseFin (G.raw.incident node) slot :=
          get_not_mem_eraseFin_of_nodup (G.raw.incident node) slot
            (G.raw.incident_nodup node)
        exact hentryNotMem (by simpa [hendpointEntry] using hnewEndpoint)
      · have holdSlot :
            G.raw.endpointEdge ((G.raw.incident node).get slot') ∉
              st.processedEdges :=
          st.unseen_incident_unprocessed node hunseen slot'
        exact holdSlot (by
          rw [hslot']
          exact hold)
  pending_owner_seen := by
    intro endpoint hmem owner howner
    simp at hmem
    rcases hmem with hrest | hnewEndpoint
    · have hstPending : endpoint ∈ st.pending := by
        rw [hpending]
        right
        exact hrest
      cases owner with
      | boundary _ =>
          trivial
      | constructor ownerNode ownerSlot =>
          have hseen : ownerNode ∈ st.seenNodes :=
            st.constructor_seen_of_pending hstPending howner
          simp [hseen]
    · have hincident : endpoint ∈ G.raw.incident node :=
        mem_of_mem_eraseFin (G.raw.incident node) slot hnewEndpoint
      rcases list_exists_get_of_mem (G.raw.incident node) hincident with
        ⟨slot', hslot'⟩
      cases owner with
      | boundary _ =>
          trivial
      | constructor ownerNode ownerSlot =>
          have hconstructorOwner :
              PortHypergraph.endpointOwnerEndpoint G.raw
                  (.constructor node slot') = endpoint := by
            simpa [PortHypergraph.endpointOwnerEndpoint] using hslot'
          rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
          have hnewEq :
              (.constructor node slot' :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) = owner₀ := by
            apply huniq
            simpa [PortHypergraph.endpointOwnerEndpoint] using hconstructorOwner
          have hownerEq :
              (.constructor ownerNode ownerSlot :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) = owner₀ := by
            apply huniq
            simpa [PortHypergraph.endpointOwnerEndpoint] using howner
          have hsame :
              (.constructor ownerNode ownerSlot :
                EndpointOwner boundary.length G.raw.nodeCount
                  (fun node => (G.raw.incident node).length)) =
                .constructor node slot' := hownerEq.trans hnewEq.symm
          cases hsame
          simp
  unseen_incident_unprocessed := by
    intro otherNode hotherUnseen otherSlot hprocessed
    have hotherNotSeen : otherNode ∉ st.seenNodes := by
      intro hseen
      exact hotherUnseen (by simp [hseen])
    simp at hprocessed
    rcases hprocessed with hnewProcessed | hold
    · let endpoint := (G.raw.incident otherNode).get otherSlot
      have hactiveNe : active ≠ endpoint := by
        intro hactiveEndpoint
        have hactivePending : active ∈ st.pending := by
          rw [hpending]
          simp
        have hseen : otherNode ∈ st.seenNodes :=
          st.constructor_seen_of_pending hactivePending (by
            change (G.raw.incident otherNode).get otherSlot = active
            exact hactiveEndpoint.symm)
        exact hotherNotSeen hseen
      have hendpointEntry :
          endpoint = (G.raw.incident node).get slot := by
        rcases PortHypergraph.edgeMate_existsUnique G.raw active with
          ⟨uniqueMate, _huniqueMate, huniq⟩
        have hmateEq : (G.raw.incident node).get slot = uniqueMate :=
          huniq ((G.raw.incident node).get slot) hmate
        have hendpointEq : endpoint = uniqueMate :=
          huniq endpoint ⟨hactiveNe, hnewProcessed.symm⟩
        exact hendpointEq.trans hmateEq.symm
      have hownerOther :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor otherNode otherSlot) =
            endpoint := rfl
      have hownerNode :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) =
            endpoint := by
        change (G.raw.incident node).get slot = endpoint
        exact hendpointEntry.symm
      rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
      have hotherEq :
          (.constructor otherNode otherSlot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) = owner₀ := by
        apply huniq
        simpa [PortHypergraph.endpointOwnerEndpoint] using hownerOther
      have hnodeEq :
          (.constructor node slot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) = owner₀ := by
        apply huniq
        simpa [PortHypergraph.endpointOwnerEndpoint] using hownerNode
      have hsame :
          (.constructor otherNode otherSlot :
            EndpointOwner boundary.length G.raw.nodeCount
              (fun node => (G.raw.incident node).length)) =
            .constructor node slot := hotherEq.trans hnodeEq.symm
      cases hsame
      exact hotherUnseen (by simp)
    · exact st.unseen_incident_unprocessed otherNode hotherNotSeen otherSlot hold

theorem budChild_frontierComplete {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes)
    (hcomplete : st.FrontierComplete) :
    (st.budChild hpending node slot hmate hunseen).FrontierComplete := by
  intro endpoint hunprocessed owner howner
  have hchildUnprocessed :
      G.raw.endpointEdge endpoint ∉
        G.raw.endpointEdge active :: st.processedEdges := by
    simpa [FrontierComplete, toTraversalState, budChild, processedEdge]
      using hunprocessed
  have hnotActiveEdge :
      G.raw.endpointEdge endpoint ≠ G.raw.endpointEdge active := by
    intro hedge
    exact hchildUnprocessed (by simp [hedge])
  have holdUnprocessed :
      G.raw.endpointEdge endpoint ∉ st.processedEdges := by
    intro hold
    exact hchildUnprocessed (by simp [hold])
  have old_pending_to_child
      (holdPending : endpoint ∈ st.pending) :
      endpoint ∈ rest ++ eraseFin (G.raw.incident node) slot := by
    have hrest : endpoint ∈ rest := by
      rw [hpending] at holdPending
      exact list_mem_tail_of_mem_cons_ne holdPending (by
        intro hactiveEndpoint
        exact hnotActiveEdge (by
          rw [← hactiveEndpoint]))
    exact List.mem_append_left _ hrest
  cases owner with
  | boundary boundaryIndex =>
      have holdPending :
          endpoint ∈ st.pending :=
        hcomplete endpoint holdUnprocessed (.boundary boundaryIndex) howner
      simpa [FrontierComplete, toTraversalState, budChild]
        using old_pending_to_child holdPending
  | constructor ownerNode ownerSlot =>
      intro hseen
      have hseen' : ownerNode ∈ node :: st.seenNodes := by
        simpa [FrontierComplete, toTraversalState, budChild, seenNode]
          using hseen
      simp at hseen'
      rcases hseen' with hnew | holdSeen
      · cases hnew
        have hownerEndpoint :
            (G.raw.incident node).get ownerSlot = endpoint := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hnotEntry :
            endpoint ≠ (G.raw.incident node).get slot := by
          intro hendpointEntry
          exact hnotActiveEdge (by
            rw [hendpointEntry]
            exact hmate.2.symm)
        have hmemIncident :
            endpoint ∈ G.raw.incident node := by
          rw [← hownerEndpoint]
          exact List.get_mem (G.raw.incident node) ownerSlot
        have hmemExcept :
            endpoint ∈ eraseFin (G.raw.incident node) slot :=
          mem_eraseFin_of_mem_ne_get (G.raw.incident node) slot
            hmemIncident hnotEntry
        exact List.mem_append_right rest hmemExcept
      · have holdPending :
            endpoint ∈ st.pending :=
          hcomplete endpoint holdUnprocessed
            (.constructor ownerNode ownerSlot) howner holdSeen
        simpa [FrontierComplete, toTraversalState, budChild, seenNode]
          using old_pending_to_child holdPending

theorem connectChild_remainingEdges_lt {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    (st.connectChild hpending mate hmate).remainingEdges < st.remainingEdges := by
  have hactive : active ∈ st.pending := by
    rw [hpending]
    simp
  have hlt := st.processedEdges_length_lt_of_pending hactive
  simp [remainingEdges, connectChild]
  omega

theorem connectChild_proof_irrel {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate₁ hmate₂ : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    st.connectChild hpending mate hmate₁ =
      st.connectChild hpending mate hmate₂ := by
  have hproof : hmate₁ = hmate₂ := Subsingleton.elim _ _
  cases hproof
  rfl

theorem budChild_remainingEdges_lt {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ st.seenNodes) :
    (st.budChild hpending node slot hmate hunseen).remainingEdges <
      st.remainingEdges := by
  have hactive : active ∈ st.pending := by
    rw [hpending]
    simp
  have hlt := st.processedEdges_length_lt_of_pending hactive
  simp [remainingEdges, budChild]
  omega

theorem budChild_proof_irrel {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate₁ hmate₂ :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen₁ hunseen₂ : node ∉ st.seenNodes) :
    st.budChild hpending node slot hmate₁ hunseen₁ =
      st.budChild hpending node slot hmate₂ hunseen₂ := by
  have hmateProof : hmate₁ = hmate₂ := Subsingleton.elim _ _
  have hunseenProof : hunseen₁ = hunseen₂ := Subsingleton.elim _ _
  cases hmateProof
  cases hunseenProof
  rfl

theorem RenderPrefixRelated.connectChild_of_new_edge
    {activeLabel : Sig.Port} {frontier : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: frontier)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: frontier)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate :
      PortHypergraph.EdgeMate ev.toOpenPortHypergraph.raw active
        (rest.get mate))
    (childRst :
      RenderState Sig (eraseFin frontier (sst.restLabelIndex hpending mate)))
    (hpendingVals :
      (sst.connectChild hpending mate hmate).pending.map
          (fun endpoint => endpoint.val) = childRst.frontierIds)
    (hactiveEdge :
      (ev.toOpenPortHypergraph.raw.endpointEdge active).val =
        rst.edges.length)
    (hedgesLength : childRst.edges.length = rst.edges.length + 1)
    (hnodesLength : childRst.nodes.length = rst.nodes.length) :
    RenderPrefixRelated ev childRst
      (sst.connectChild hpending mate hmate) where
  pending_vals := hpendingVals
  processed_prefix := by
    intro edge
    constructor
    · intro hmem
      simp [connectChild] at hmem
      rcases hmem with hnew | hold
      · have hval : edge.val = rst.edges.length := by
          rw [hnew]
          exact hactiveEdge
        omega
      · have holdLt := (hrel.processed_prefix edge).1 hold
        omega
    · intro hlt
      have hlt' : edge.val < rst.edges.length + 1 := by
        simpa [hedgesLength] using hlt
      have hcases : edge.val < rst.edges.length ∨
          edge.val = rst.edges.length := by
        omega
      simp [connectChild]
      rcases hcases with hold | hnew
      · right
        exact (hrel.processed_prefix edge).2 hold
      · left
        apply Fin.ext
        exact hnew.trans hactiveEdge.symm
  seen_prefix := by
    intro node
    constructor
    · intro hmem
      simp [connectChild] at hmem
      have hlt := (hrel.seen_prefix node).1 hmem
      omega
    · intro hlt
      simp [connectChild]
      have hltOld : node.val < rst.nodes.length := by
        omega
      exact (hrel.seen_prefix node).2 hltOld

theorem RenderPrefixRelated.budChild_of_new_edge_node
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {final : RenderState Sig []}
    {ev : RenderState.OpenPortHypergraphEvidence final boundary}
    {rst : RenderState Sig (activeLabel :: restLabels)}
    {sst : SearchState ev.toOpenPortHypergraph (activeLabel :: restLabels)}
    (hrel : RenderPrefixRelated ev rst sst)
    {active : Fin ev.toOpenPortHypergraph.raw.endpointCount}
    {rest : List (Fin ev.toOpenPortHypergraph.raw.endpointCount)}
    (hpending : sst.pending = active :: rest)
    (node : Fin ev.toOpenPortHypergraph.raw.nodeCount)
    (slot : Fin (ev.toOpenPortHypergraph.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate ev.toOpenPortHypergraph.raw active
        ((ev.toOpenPortHypergraph.raw.incident node).get slot))
    (hunseen : node ∉ sst.seenNodes)
    (childRst :
      RenderState Sig
        (restLabels ++
          Sig.nodePortsExcept (ev.toOpenPortHypergraph.raw.nodeLabel node)
            (budEntry node slot)))
    (hpendingVals :
      (sst.budChild hpending node slot hmate hunseen).pending.map
          (fun endpoint => endpoint.val) = childRst.frontierIds)
    (hactiveEdge :
      (ev.toOpenPortHypergraph.raw.endpointEdge active).val =
        rst.edges.length)
    (hnewNode : node.val = rst.nodes.length)
    (hedgesLength : childRst.edges.length = rst.edges.length + 1)
    (hnodesLength : childRst.nodes.length = rst.nodes.length + 1) :
    RenderPrefixRelated ev childRst
      (sst.budChild hpending node slot hmate hunseen) where
  pending_vals := hpendingVals
  processed_prefix := by
    intro edge
    constructor
    · intro hmem
      simp [budChild] at hmem
      rcases hmem with hnew | hold
      · have hval : edge.val = rst.edges.length := by
          rw [hnew]
          exact hactiveEdge
        omega
      · have holdLt := (hrel.processed_prefix edge).1 hold
        omega
    · intro hlt
      have hlt' : edge.val < rst.edges.length + 1 := by
        simpa [hedgesLength] using hlt
      have hcases : edge.val < rst.edges.length ∨
          edge.val = rst.edges.length := by
        omega
      simp [budChild]
      rcases hcases with hold | hnew
      · right
        exact (hrel.processed_prefix edge).2 hold
      · left
        apply Fin.ext
        exact hnew.trans hactiveEdge.symm
  seen_prefix := by
    intro candidate
    constructor
    · intro hmem
      simp [budChild] at hmem
      rcases hmem with hnew | hold
      · have hval : candidate.val = rst.nodes.length := by
          rw [hnew]
          exact hnewNode
        omega
      · have holdLt := (hrel.seen_prefix candidate).1 hold
        omega
    · intro hlt
      have hlt' : candidate.val < rst.nodes.length + 1 := by
        simpa [hnodesLength] using hlt
      have hcases : candidate.val < rst.nodes.length ∨
          candidate.val = rst.nodes.length := by
        omega
      simp [budChild]
      rcases hcases with hold | hnew
      · right
        exact (hrel.seen_prefix candidate).2 hold
      · left
        apply Fin.ext
        exact hnew.trans hnewNode.symm

theorem IsoRelated.connectChild
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    let rightPending := hr.pending_cons hpending
    let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
      Fin.cast (by simp) mate
    let rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((rest.map e.endpointEquiv.toFun).get rightMate) := by
      have hget :
          (rest.map e.endpointEquiv.toFun).get rightMate =
            e.endpointEquiv.toFun (rest.get mate) := by
        simp [rightMate]
      rw [hget]
      exact PortHypergraphIso.edgeMate_preserved e hmate
    IsoRelated e
      (left.connectChild hpending mate hmate)
      (right.connectChild rightPending rightMate rightMateEdge) := by
  dsimp
  constructor
  · exact (map_eraseFin e.endpointEquiv.toFun rest mate).symm
  · exact hr.seenNodes_eq
  · change H.raw.endpointEdge (e.endpointEquiv.toFun active) ::
        right.processedEdges =
      (G.raw.endpointEdge active :: left.processedEdges).map
        e.edgeEquiv.toFun
    rw [e.endpoint_edge_preserved active, hr.processedEdges_eq]
    rfl

theorem IsoRelated.connectChild_with
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((rest.map e.endpointEquiv.toFun).get (Fin.cast (by simp) mate))) :
    IsoRelated e
      (left.connectChild hpending mate hmate)
      (right.connectChild (hr.pending_cons hpending)
        (Fin.cast (by simp) mate) rightMateEdge) := by
  have hbase := hr.connectChild hpending mate hmate
  dsimp at hbase
  have hchild :
      right.connectChild (hr.pending_cons hpending)
          (Fin.cast (by simp) mate) (by
            have hget :
                (rest.map e.endpointEquiv.toFun).get (Fin.cast (by simp) mate) =
                  e.endpointEquiv.toFun (rest.get mate) := by
              simp
            rw [hget]
            exact PortHypergraphIso.edgeMate_preserved e hmate) =
        right.connectChild (hr.pending_cons hpending)
          (Fin.cast (by simp) mate) rightMateEdge := by
    exact right.connectChild_proof_irrel (hr.pending_cons hpending)
      (Fin.cast (by simp) mate) _ rightMateEdge
  rw [← hchild]
  exact hbase

theorem IsoRelated.budChild
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ left.seenNodes) :
    let rightPending := hr.pending_cons hpending
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    let rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((H.raw.incident rightNode).get rightSlot) := by
      have hslot :
          (H.raw.incident rightNode).get rightSlot =
            e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
        PortHypergraphIso.incidence_get_preserved e node slot
      rw [hslot]
      exact PortHypergraphIso.edgeMate_preserved e hmate
    let rightUnseen : rightNode ∉ right.seenNodes := by
      intro hseen
      have hpre := hr.seen_mem_reflected hseen
      exact hunseen (by simpa [rightNode] using hpre)
    let hfrontier :
        restLabels ++
            Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
              (budEntry (G := H) rightNode rightSlot) =
          restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node)
              (budEntry (G := G) node slot) := by
      have hentryVal :
          (budEntry (G := H) (e.nodeEquiv.toFun node)
              (PortHypergraphIso.incidenceSlotPreserved e node slot)).val =
            (budEntry (G := G) node slot).val := by
        simp [budEntry, PortHypergraphIso.incidenceSlotPreserved]
      exact congrArg (fun tail => restLabels ++ tail)
        (nodePortsExcept_eq_of_val
          (e.node_label_preserved node).symm hentryVal)
    IsoRelated e
      (left.budChild hpending node slot hmate hunseen)
      (hfrontier ▸
        right.budChild rightPending rightNode rightSlot rightMateEdge
          rightUnseen) := by
  dsimp
  constructor
  · rw [cast_pending]
    calc
      rest.map e.endpointEquiv.toFun ++
          eraseFin (H.raw.incident (e.nodeEquiv.toFun node))
            (PortHypergraphIso.incidenceSlotPreserved e node slot) =
        rest.map e.endpointEquiv.toFun ++
          eraseFin ((G.raw.incident node).map e.endpointEquiv.toFun)
            (Fin.cast (by simp) slot) := by
          congr 1
          have hincident :
              H.raw.incident (e.nodeEquiv.toFun node) =
                (G.raw.incident node).map e.endpointEquiv.toFun :=
            (e.incidence_preserved node).symm
          rw [eraseFin_eq_of_eq hincident
            (PortHypergraphIso.incidenceSlotPreserved e node slot)]
          apply congrArg
          apply Fin.ext
          rfl
      _ = rest.map e.endpointEquiv.toFun ++
          (eraseFin (G.raw.incident node) slot).map e.endpointEquiv.toFun := by
          rw [map_eraseFin]
      _ =
          (rest ++ eraseFin (G.raw.incident node) slot).map
            e.endpointEquiv.toFun := by
          rw [List.map_append]
  · rw [cast_seenNodes]
    change e.nodeEquiv.toFun node :: right.seenNodes =
      (node :: left.seenNodes).map e.nodeEquiv.toFun
    rw [hr.seenNodes_eq]
    rfl
  · rw [cast_processedEdges]
    change H.raw.endpointEdge (e.endpointEquiv.toFun active) ::
        right.processedEdges =
      (G.raw.endpointEdge active :: left.processedEdges).map
        e.edgeEquiv.toFun
    rw [e.endpoint_edge_preserved active, hr.processedEdges_eq]
    rfl

theorem IsoRelated.budChild_with
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : node ∉ left.seenNodes)
    (rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((H.raw.incident (e.nodeEquiv.toFun node)).get
          (PortHypergraphIso.incidenceSlotPreserved e node slot)))
    (rightUnseen : e.nodeEquiv.toFun node ∉ right.seenNodes) :
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    let hfrontier :
        restLabels ++
            Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
              (budEntry (G := H) rightNode rightSlot) =
          restLabels ++
            Sig.nodePortsExcept (G.raw.nodeLabel node)
              (budEntry (G := G) node slot) := by
      have hentryVal := budEntry_val_preserved e node slot
      exact congrArg (fun tail => restLabels ++ tail)
        (nodePortsExcept_eq_of_val
          (e.node_label_preserved node).symm hentryVal)
    IsoRelated e
      (left.budChild hpending node slot hmate hunseen)
      (hfrontier ▸
        right.budChild (hr.pending_cons hpending) rightNode rightSlot
          rightMateEdge rightUnseen) := by
  dsimp
  have hbase := hr.budChild hpending node slot hmate hunseen
  dsimp at hbase
  have hmateProof :
      (by
        have hslot :
            (H.raw.incident (e.nodeEquiv.toFun node)).get
                (PortHypergraphIso.incidenceSlotPreserved e node slot) =
              e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
          PortHypergraphIso.incidence_get_preserved e node slot
        rw [hslot]
        exact PortHypergraphIso.edgeMate_preserved e hmate) =
      rightMateEdge := Subsingleton.elim _ _
  have hunseenProof :
      (by
        intro hseen
        have hpre := hr.seen_mem_reflected hseen
        exact hunseen (by simpa [seenNode] using hpre)) =
      rightUnseen := Subsingleton.elim _ _
  cases hmateProof
  cases hunseenProof
  exact hbase

end SearchState

/--
Search the ordered pending tail for a `connect` step.  A successful result
carries the exact mate index and edge-mate proof consumed by `Diag.connect`.
-/
def firstPendingConnectSearch? (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G seenNode active rest) :=
  (List.finRange rest.length).findSome? fun mate =>
    match PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate) with
    | some hmate => some (FirstPendingStep.connect mate hmate.proof)
    | none => none

theorem firstPendingConnectSearch?_exists_of_witness
    (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ step : FirstPendingStep G seenNode active rest,
      firstPendingConnectSearch? G seenNode active rest = some step := by
  unfold firstPendingConnectSearch?
  apply findSome?_exists_of_mem_isSome
  · exact List.mem_finRange mate
  · have hcandidate :
        (PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate)).isSome :=
      PortHypergraph.edgeMateCandidate?_isSome_of_edgeMate G.raw hmate
    cases hcase :
        PortHypergraph.edgeMateCandidate? G.raw active (rest.get mate) with
    | none =>
        rw [hcase] at hcandidate
        simp at hcandidate
    | some data =>
        simp

theorem firstPendingConnectSearch?_some_connect
    (G : OpenPortHypergraph Sig boundary)
    (seenNode : Fin G.raw.nodeCount → Prop)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G seenNode active rest}
    (hstep : firstPendingConnectSearch? G seenNode active rest = some step) :
    ∃ (mate : Fin rest.length)
      (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)),
      step = FirstPendingStep.connect mate hmate := by
  unfold firstPendingConnectSearch? at hstep
  rcases List.exists_of_findSome?_eq_some hstep with
    ⟨mate, _hmem, hcandidate⟩
  cases hcase : PortHypergraph.edgeMateCandidate? G.raw active
      (rest.get mate) with
  | none =>
      rw [hcase] at hcandidate
      cases hcandidate
  | some data =>
      rw [hcase] at hcandidate
      injection hcandidate with hstepEq
      exact ⟨mate, data.proof, hstepEq.symm⟩

namespace SearchState

/--
Search unseen constructors in representative order for a `bud` step.  The
successful slot is the constructor port joined to the active endpoint.
-/
def firstPendingBudSearch? {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G st.seenNode active rest) :=
  (List.finRange G.raw.nodeCount).findSome? fun node =>
    if hseen : node ∈ st.seenNodes then
      none
    else
      (List.finRange (G.raw.incident node).length).findSome? fun slot =>
        match PortHypergraph.edgeMateCandidate? G.raw active
            ((G.raw.incident node).get slot) with
        | some hmate =>
            some (FirstPendingStep.bud node slot hmate.proof
              (by simpa [seenNode] using hseen))
        | none => none

theorem firstPendingBudSearch?_exists_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingBudSearch? active rest = some step := by
  unfold firstPendingBudSearch?
  apply findSome?_exists_of_mem_isSome
  · exact List.mem_finRange node
  · have hnodeUnseen : node ∉ st.seenNodes := by
      simpa [seenNode] using hunseen
    simp [hnodeUnseen]
    refine ⟨slot, ?_⟩
    have hcandidate :
        (PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot)).isSome :=
      PortHypergraph.edgeMateCandidate?_isSome_of_edgeMate G.raw hmate
    cases hcase :
        PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot) with
    | none =>
        rw [hcase] at hcandidate
        simp at hcandidate
    | some data =>
        simp

theorem firstPendingBudSearch?_some_bud
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G st.seenNode active rest}
    (hstep : st.firstPendingBudSearch? active rest = some step) :
    ∃ (node : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident node).length)
      (hmate :
        PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (hunseen : ¬ st.seenNode node),
      step = FirstPendingStep.bud node slot hmate hunseen := by
  unfold firstPendingBudSearch? at hstep
  rcases List.exists_of_findSome?_eq_some hstep with
    ⟨node, _hnodeMem, hnodeCandidate⟩
  by_cases hseen : node ∈ st.seenNodes
  · simp [hseen] at hnodeCandidate
  · simp [hseen] at hnodeCandidate
    rcases List.exists_of_findSome?_eq_some hnodeCandidate with
      ⟨slot, _hslotMem, hslotCandidate⟩
    change
      (match PortHypergraph.edgeMateCandidate? G.raw active
          ((G.raw.incident node).get slot) with
        | some hmate => some (FirstPendingStep.bud node slot
            hmate.proof (by simpa [seenNode] using hseen))
        | none => none) = some step at hslotCandidate
    cases hcase : PortHypergraph.edgeMateCandidate? G.raw active
        ((G.raw.incident node).get slot) with
    | none =>
        rw [hcase] at hslotCandidate
        cases hslotCandidate
    | some data =>
        rw [hcase] at hslotCandidate
        injection hslotCandidate with hstepEq
        exact ⟨node, slot, data.proof, by simpa [seenNode] using hseen,
          hstepEq.symm⟩

/--
Executable first-pending search.  It tries the remaining pending frontier
first, then unseen constructor ports.  The returned value is constructor data,
not an eliminated `Prop` witness.
-/
def firstPendingStepSearch? {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (active : Fin G.raw.endpointCount)
    (rest : List (Fin G.raw.endpointCount)) :
    Option (FirstPendingStep G st.seenNode active rest) :=
  match firstPendingConnectSearch? G st.seenNode active rest with
  | some step => some step
  | none => st.firstPendingBudSearch? active rest

/-- A successful bud result from the executable first-pending search certifies
that the pending-tail connect search failed. -/
theorem firstPendingConnectSearch?_none_of_firstPendingStepSearch?_bud
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {node : Fin G.raw.nodeCount}
    {slot : Fin (G.raw.incident node).length}
    {hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot)}
    {hunseen : ¬ st.seenNode node}
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate hunseen)) :
    firstPendingConnectSearch? G st.seenNode active rest = none := by
  unfold firstPendingStepSearch? at hstep
  cases hconnect :
      firstPendingConnectSearch? G st.seenNode active rest with
  | none => rfl
  | some step =>
      rcases firstPendingConnectSearch?_some_connect
          G st.seenNode hconnect with
        ⟨mate, hmate, hstepEq⟩
      rw [hconnect, hstepEq] at hstep
      cases hstep

theorem firstPendingStepSearch?_ready
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    {step : FirstPendingStep G st.seenNode active rest}
    (_hstep : st.firstPendingStepSearch? active rest = some step) :
    FirstPendingStepReady G st.seenNode active rest :=
  step.ready

theorem firstPendingStepSearch?_exists_of_ready
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hready : FirstPendingStepReady G st.seenNode active rest) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingStepSearch? active rest = some step := by
  rcases hready with hconnect | hbud
  · rcases hconnect with ⟨mate, hmate⟩
    rcases firstPendingConnectSearch?_exists_of_witness
        G st.seenNode mate hmate with ⟨step, hstep⟩
    unfold firstPendingStepSearch?
    rw [hstep]
    exact ⟨step, rfl⟩
  · rcases hbud with ⟨node, slot, hmate, hunseen⟩
    unfold firstPendingStepSearch?
    cases hconnect :
        firstPendingConnectSearch? G st.seenNode active rest with
    | some step =>
        exact ⟨step, rfl⟩
    | none =>
        rcases st.firstPendingBudSearch?_exists_of_witness
            node slot hmate hunseen with ⟨step, hstep⟩
        exact ⟨step, by simp [hstep]⟩

theorem firstPendingStepSearch?_some_connect_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ (mate' : Fin rest.length)
      (hmate' : PortHypergraph.EdgeMate G.raw active (rest.get mate')),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate' hmate') := by
  rcases firstPendingConnectSearch?_exists_of_witness
      G st.seenNode mate hmate with ⟨step, hstep⟩
  rcases firstPendingConnectSearch?_some_connect
      G st.seenNode hstep with ⟨mate', hmate', hstepEq⟩
  unfold firstPendingStepSearch?
  rw [hstep]
  exact ⟨mate', hmate', by simp [hstepEq]⟩

theorem firstPendingStepSearch?_some_connect_exact_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hrestNodup : rest.Nodup)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    ∃ hmate' : PortHypergraph.EdgeMate G.raw active (rest.get mate),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate hmate') := by
  rcases st.firstPendingStepSearch?_some_connect_of_witness mate hmate with
    ⟨mate', hmate', hstep⟩
  have hget : rest.get mate' = rest.get mate := by
    rcases PortHypergraph.edgeMate_existsUnique G.raw active with
      ⟨uniqueMate, _huniqueMate, huniq⟩
    exact (huniq (rest.get mate') hmate').trans
      (huniq (rest.get mate) hmate).symm
  have hmateEq : mate' = mate :=
    list_get_injective_of_nodup rest hrestNodup hget
  subst mate'
  exact ⟨hmate', hstep⟩

theorem IsoRelated.firstPendingStepSearch?_connect
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate)) :
    let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
      Fin.cast (by simp) mate
    ∃ rightMateEdge :
        PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
          ((rest.map e.endpointEquiv.toFun).get rightMate),
      right.firstPendingStepSearch? (e.endpointEquiv.toFun active)
          (rest.map e.endpointEquiv.toFun) =
        some (FirstPendingStep.connect rightMate rightMateEdge) := by
  dsimp
  let rightMate : Fin (rest.map e.endpointEquiv.toFun).length :=
    Fin.cast (by simp) mate
  have hget :
      (rest.map e.endpointEquiv.toFun).get rightMate =
        e.endpointEquiv.toFun (rest.get mate) := by
    simp [rightMate]
  have rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((rest.map e.endpointEquiv.toFun).get rightMate) := by
    rw [hget]
    exact PortHypergraphIso.edgeMate_preserved e hmate
  have hrightPending := hr.pending_cons hpending
  have hrightNodup :
      (rest.map e.endpointEquiv.toFun).Nodup :=
    right.rest_nodup hrightPending
  rcases right.firstPendingStepSearch?_some_connect_exact_of_witness
      hrightNodup rightMate rightMateEdge with
    ⟨rightMateEdge', hstep⟩
  exact ⟨rightMateEdge', hstep⟩

theorem IsoRelated.firstPendingConnectSearch?_none
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (_hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (_hpending : left.pending = active :: rest)
    (hconnect :
      firstPendingConnectSearch? G left.seenNode active rest = none) :
    firstPendingConnectSearch? H right.seenNode (e.endpointEquiv.toFun active)
        (rest.map e.endpointEquiv.toFun) = none := by
  cases hright :
      firstPendingConnectSearch? H right.seenNode
        (e.endpointEquiv.toFun active) (rest.map e.endpointEquiv.toFun) with
  | none => rfl
  | some step =>
      rcases firstPendingConnectSearch?_some_connect
          H right.seenNode hright with
        ⟨rightMate, hmateRight, _hstepEq⟩
      let leftMate : Fin rest.length :=
        Fin.cast (by simp) rightMate
      have hget :
          (rest.map e.endpointEquiv.toFun).get rightMate =
            e.endpointEquiv.toFun (rest.get leftMate) := by
        simp [leftMate]
      have hmateRight' :
          PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
            (e.endpointEquiv.toFun (rest.get leftMate)) := by
        simpa [hget] using hmateRight
      have hmateLeft :
          PortHypergraph.EdgeMate G.raw active (rest.get leftMate) := by
        have hreflected := PortHypergraphIso.edgeMate_reflected e hmateRight'
        simpa using hreflected
      rcases firstPendingConnectSearch?_exists_of_witness
          G left.seenNode leftMate hmateLeft with
        ⟨leftStep, hleftStep⟩
      rw [hconnect] at hleftStep
      cases hleftStep

theorem firstPendingStepSearch?_some_bud_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hconnect :
      firstPendingConnectSearch? G st.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ (node' : Fin G.raw.nodeCount)
      (slot' : Fin (G.raw.incident node').length)
      (hmate' :
        PortHypergraph.EdgeMate G.raw active
          ((G.raw.incident node').get slot'))
      (hunseen' : ¬ st.seenNode node'),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node' slot' hmate' hunseen') := by
  rcases st.firstPendingBudSearch?_exists_of_witness
      node slot hmate hunseen with ⟨step, hstep⟩
  rcases st.firstPendingBudSearch?_some_bud hstep with
    ⟨node', slot', hmate', hunseen', hstepEq⟩
  unfold firstPendingStepSearch?
  rw [hconnect, hstep]
  exact ⟨node', slot', hmate', hunseen', by simp [hstepEq]⟩

theorem firstPendingStepSearch?_some_bud_exact_of_witness
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hconnect :
      firstPendingConnectSearch? G st.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node) :
    ∃ (hmate' :
          PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
      (hunseen' : ¬ st.seenNode node),
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate' hunseen') := by
  rcases st.firstPendingStepSearch?_some_bud_of_witness
      hconnect node slot hmate hunseen with
    ⟨node', slot', hmate', hunseen', hstep⟩
  have hendpointEq :
      (G.raw.incident node').get slot' = (G.raw.incident node).get slot := by
    rcases PortHypergraph.edgeMate_existsUnique G.raw active with
      ⟨uniqueMate, _huniqueMate, huniq⟩
    exact (huniq ((G.raw.incident node').get slot') hmate').trans
      (huniq ((G.raw.incident node).get slot) hmate).symm
  have hownerEq :
      (.constructor node' slot' :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) =
      (.constructor node slot :
        EndpointOwner boundary.length G.raw.nodeCount
          (fun node => (G.raw.incident node).length)) := by
    let endpoint := (G.raw.incident node).get slot
    rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
    have hleft :
        (.constructor node' slot' :
          EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      exact hendpointEq
    have hright :
        (.constructor node slot :
          EndpointOwner boundary.length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      rfl
    exact hleft.trans hright.symm
  cases hownerEq
  exact ⟨hmate', hunseen', hstep⟩

theorem IsoRelated.firstPendingStepSearch?_bud
    {G H : OpenPortHypergraph Sig boundary}
    {e : PortHypergraphIso G.raw H.raw}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    {left : SearchState G (activeLabel :: restLabels)}
    {right : SearchState H (activeLabel :: restLabels)}
    (hr : IsoRelated e left right)
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hpending : left.pending = active :: rest)
    (hconnect :
      firstPendingConnectSearch? G left.seenNode active rest = none)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ left.seenNode node) :
    let rightNode := e.nodeEquiv.toFun node
    let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
    ∃ (rightMateEdge :
          PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
            ((H.raw.incident rightNode).get rightSlot))
      (rightUnseen : ¬ right.seenNode rightNode),
      right.firstPendingStepSearch? (e.endpointEquiv.toFun active)
          (rest.map e.endpointEquiv.toFun) =
        some (FirstPendingStep.bud rightNode rightSlot rightMateEdge
          rightUnseen) := by
  dsimp
  let rightNode := e.nodeEquiv.toFun node
  let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
  have rightMateEdge :
      PortHypergraph.EdgeMate H.raw (e.endpointEquiv.toFun active)
        ((H.raw.incident rightNode).get rightSlot) := by
    have hslot :
        (H.raw.incident rightNode).get rightSlot =
          e.endpointEquiv.toFun ((G.raw.incident node).get slot) :=
      PortHypergraphIso.incidence_get_preserved e node slot
    rw [hslot]
    exact PortHypergraphIso.edgeMate_preserved e hmate
  have rightUnseen : ¬ right.seenNode rightNode := by
    intro hseen
    have hpre := hr.seen_mem_reflected hseen
    exact hunseen (by simpa [rightNode, seenNode] using hpre)
  have hconnectRight :=
    hr.firstPendingConnectSearch?_none hpending hconnect
  rcases right.firstPendingStepSearch?_some_bud_exact_of_witness
      hconnectRight rightNode rightSlot rightMateEdge rightUnseen with
    ⟨rightMateEdge', rightUnseen', hstep⟩
  exact ⟨rightMateEdge', rightUnseen', hstep⟩

end SearchState

/--
The global traversal-readiness invariant for an open representative.  It is
the missing totality statement for the owned graph-to-`Diag` search: every
nonempty ordered pending state has the constructor choice required by the
syntax.
-/
def FirstPendingTraversalReady (G : OpenPortHypergraph Sig boundary) : Prop :=
  ∀ {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : TraversalState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)},
    st.FrontierComplete →
    st.pending = active :: rest →
      FirstPendingStepReady G st.seenNode active rest

/--
Frontier completeness makes the first-pending traversal step locally total.
Initial completeness and step preservation are the remaining state-invariant
obligations for the owned graph-to-`Diag` traversal.
-/
theorem firstPendingTraversalReady_of_frontierComplete
    (G : OpenPortHypergraph Sig boundary) :
    FirstPendingTraversalReady G := by
  intro activeLabel restLabels st active rest hcomplete hpending
  rcases PortHypergraph.edgeMate_existsUnique G.raw active with
    ⟨mate, hmate, _hmateUniq⟩
  have hactiveMem : active ∈ st.pending := by
    rw [hpending]
    simp
  have hactiveUnprocessed :
      ¬ st.processedEdge (G.raw.endpointEdge active) :=
    st.pending_unprocessed active hactiveMem
  have hmateUnprocessed :
      ¬ st.processedEdge (G.raw.endpointEdge mate) := by
    intro hprocessed
    exact hactiveUnprocessed (by simpa [hmate.2] using hprocessed)
  have mate_pending_tail
      (hmatePending : mate ∈ st.pending) : mate ∈ rest := by
    rw [hpending] at hmatePending
    exact list_mem_tail_of_mem_cons_ne hmatePending (by
      intro hactiveMate
      exact hmate.1 hactiveMate)
  have connect_of_pending (hmatePending : mate ∈ st.pending) :
      FirstPendingStepReady G st.seenNode active rest := by
    have hrest : mate ∈ rest := mate_pending_tail hmatePending
    rcases list_exists_get_of_mem rest hrest with ⟨mateIndex, hget⟩
    refine Or.inl ⟨mateIndex, ?_⟩
    rw [hget]
    exact hmate
  rcases G.raw.endpoint_owner mate with ⟨owner, howner, _huniq⟩
  cases owner with
  | boundary boundaryIndex =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.boundary boundaryIndex) = mate := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      exact connect_of_pending
        (hcomplete mate hmateUnprocessed (.boundary boundaryIndex)
          hownerEndpoint)
  | constructor node slot =>
      have hownerEndpoint :
          PortHypergraph.endpointOwnerEndpoint G.raw
              (.constructor node slot) = mate := by
        simpa [PortHypergraph.endpointOwnerEndpoint] using howner
      by_cases hseen : st.seenNode node
      · exact connect_of_pending
          (hcomplete mate hmateUnprocessed (.constructor node slot)
            hownerEndpoint hseen)
      · refine Or.inr ⟨node, slot, ?_, hseen⟩
        rw [show (G.raw.incident node).get slot = mate by
          simpa [PortHypergraph.endpointOwnerEndpoint] using hownerEndpoint]
        exact hmate

/--
A finite search state inherits first-pending step readiness from its projected
proof-level traversal state.  This still returns a `Prop`; the data-producing
search must construct `FirstPendingStep` directly.
-/
theorem SearchState.firstPendingStepReady_of_frontierComplete
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount} {rest : List (Fin G.raw.endpointCount)}
    (hcomplete : st.FrontierComplete)
    (hpending : st.pending = active :: rest) :
      FirstPendingStepReady G st.seenNode active rest :=
  (firstPendingTraversalReady_of_frontierComplete G)
    st.toTraversalState hcomplete hpending

theorem SearchState.firstPendingStepSearch?_exists_of_frontierComplete
    {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hcomplete : st.FrontierComplete)
    (hpending : st.pending = active :: rest) :
    ∃ step : FirstPendingStep G st.seenNode active rest,
      st.firstPendingStepSearch? active rest = some step :=
  st.firstPendingStepSearch?_exists_of_ready
    (st.firstPendingStepReady_of_frontierComplete hcomplete hpending)

namespace SearchState

/--
Owned graph-to-syntax traversal from a finite search state.  The recursion
always processes the first pending endpoint.  The `none` search branch is
impossible by `firstPendingStepSearch?_exists_of_frontierComplete`, and child
recursion decreases the finite count of unprocessed edges.
-/
def toDiag {G : OpenPortHypergraph Sig boundary} :
    ∀ {frontier : List Sig.Port},
      (st : SearchState G frontier) → st.FrontierComplete → Diag Sig frontier
  | [], _st, _hcomplete => Diag.finish
  | activeLabel :: restLabels, st, hcomplete =>
      match hpending : st.pending with
      | [] =>
          False.elim (by
            have hlabels := st.pending_labels
            rw [hpending] at hlabels
            simp at hlabels)
      | active :: rest =>
          match hstep : st.firstPendingStepSearch? active rest with
          | none =>
              False.elim (by
                rcases st.firstPendingStepSearch?_exists_of_frontierComplete
                    hcomplete hpending with ⟨step, hsome⟩
                rw [hstep] at hsome
                cases hsome)
          | some step =>
              match step with
              | FirstPendingStep.connect mate hmate =>
                  Diag.connect
                    (st.restLabelIndex hpending mate)
                    (st.connect_compatible hpending mate hmate)
                    (toDiag
                      (st.connectChild hpending mate hmate)
                      (st.connectChild_frontierComplete hpending mate hmate
                        hcomplete))
              | FirstPendingStep.bud node slot hmate hunseen =>
                  Diag.bud
                    (G.raw.nodeLabel node)
                    (budEntry node slot)
                    (st.bud_compatible hpending node slot hmate)
                    (toDiag
                      (st.budChild hpending node slot hmate
                        (by simpa [seenNode] using hunseen))
                      (st.budChild_frontierComplete hpending node slot hmate
                        (by simpa [seenNode] using hunseen) hcomplete))
termination_by frontier st _hcomplete => st.remainingEdges
decreasing_by
  · exact st.connectChild_remainingEdges_lt hpending mate hmate
  · exact st.budChild_remainingEdges_lt hpending node slot hmate
      (by simpa [seenNode] using hunseen)

/-- The owned traversal result is independent of the proof of frontier
completeness supplied to it. -/
theorem toDiag_frontierComplete_irrel {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port}
    (st : SearchState G frontier)
    (h₁ h₂ : st.FrontierComplete) :
    st.toDiag h₁ = st.toDiag h₂ := by
  have hproof : h₁ = h₂ := Subsingleton.elim _ _
  cases hproof
  rfl

/-- Traversal commutes with casting the frontier index of a search state. -/
theorem toDiag_cast {G : OpenPortHypergraph Sig boundary}
    {frontier frontier' : List Sig.Port}
    (h : frontier = frontier') (st : SearchState G frontier)
    (hc : st.FrontierComplete) :
    (h ▸ st).toDiag (frontierComplete_cast h st hc) =
      h ▸ st.toDiag hc := by
  cases h
  rfl

/-- Empty-frontier traversal computes to `finish`. -/
theorem toDiag_empty {G : OpenPortHypergraph Sig boundary}
    (st : SearchState G []) (hcomplete : st.FrontierComplete) :
    st.toDiag hcomplete = Diag.finish := by
  rw [SearchState.toDiag.eq_def]

/-- Connect-branch computation rule for the owned first-pending traversal. -/
theorem toDiag_connect {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    (hcomplete : st.FrontierComplete)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (mate : Fin rest.length)
    (hmate : PortHypergraph.EdgeMate G.raw active (rest.get mate))
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.connect mate hmate)) :
    st.toDiag hcomplete =
      Diag.connect
        (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate)
        ((st.connectChild hpending mate hmate).toDiag
          (st.connectChild_frontierComplete hpending mate hmate hcomplete)) := by
  rw [SearchState.toDiag.eq_2]
  split
  · rename_i hnil
    rw [hnil] at hpending
    cases hpending
  · rename_i active' rest' hp
    have hcons : active' :: rest' = active :: rest := by
      rw [← hpending, hp]
    injection hcons with hactive hrest
    subst active'
    subst rest'
    split
    · rename_i hnone
      rw [hstep] at hnone
      cases hnone
    · rename_i step hstep'
      cases step with
      | connect mate' hmate' =>
          rw [hstep] at hstep'
          injection hstep' with hconnect
          cases hconnect
          simp
      | bud _node _slot _hmate' _hunseen =>
          rw [hstep] at hstep'
          cases hstep'

/-- Bud-branch computation rule for the owned first-pending traversal. -/
theorem toDiag_bud {G : OpenPortHypergraph Sig boundary}
    {activeLabel : Sig.Port} {restLabels : List Sig.Port}
    (st : SearchState G (activeLabel :: restLabels))
    (hcomplete : st.FrontierComplete)
    {active : Fin G.raw.endpointCount}
    {rest : List (Fin G.raw.endpointCount)}
    (hpending : st.pending = active :: rest)
    (node : Fin G.raw.nodeCount)
    (slot : Fin (G.raw.incident node).length)
    (hmate :
      PortHypergraph.EdgeMate G.raw active ((G.raw.incident node).get slot))
    (hunseen : ¬ st.seenNode node)
    (hstep :
      st.firstPendingStepSearch? active rest =
        some (FirstPendingStep.bud node slot hmate hunseen)) :
    st.toDiag hcomplete =
      Diag.bud
        (G.raw.nodeLabel node)
        (budEntry node slot)
        (st.bud_compatible hpending node slot hmate)
        ((st.budChild hpending node slot hmate
            (by simpa [seenNode] using hunseen)).toDiag
          (st.budChild_frontierComplete hpending node slot hmate
            (by simpa [seenNode] using hunseen) hcomplete)) := by
  rw [SearchState.toDiag.eq_2]
  split
  · rename_i hnil
    rw [hnil] at hpending
    cases hpending
  · rename_i active' rest' hp
    have hcons : active' :: rest' = active :: rest := by
      rw [← hpending, hp]
    injection hcons with hactive hrest
    subst active'
    subst rest'
    split
    · rename_i hnone
      rw [hstep] at hnone
      cases hnone
    · rename_i step hstep'
      cases step with
      | connect _mate' _hmate' =>
          rw [hstep] at hstep'
          cases hstep'
      | bud _node' _slot' _hmate' _hunseen' =>
          rw [hstep] at hstep'
          injection hstep' with hbud
          cases hbud
          simp

/-- The owned graph-to-syntax traversal is invariant under related
ordered-boundary-preserving isomorphic search states. -/
theorem toDiag_isoRelated
    {G H : OpenPortHypergraph Sig boundary}
    (e : PortHypergraphIso G.raw H.raw)
    {frontier : List Sig.Port}
    (left : SearchState G frontier) (right : SearchState H frontier)
    (hrel : IsoRelated e left right)
    (hleft : left.FrontierComplete) (hright : right.FrontierComplete) :
    left.toDiag hleft = right.toDiag hright := by
  induction frontier, left, hleft using SearchState.toDiag.induct with
  | case1 st hcomplete _hcomplete =>
      rw [toDiag_empty]
      rw [toDiag_empty]
  | case2 activeLabel restLabels active rest mate hmate st _hcomplete
      hcomplete hpending hstep _hstep ih =>
      have hrightPending := hrel.pending_cons hpending
      rcases hrel.firstPendingStepSearch?_connect hpending mate hmate with
        ⟨rightMateEdge, hrightStep⟩
      have hchildRel :=
        hrel.connectChild_with hpending mate hmate rightMateEdge
      have hchild :=
        ih (right.connectChild hrightPending (Fin.cast (by simp) mate)
              rightMateEdge) hchildRel
          (right.connectChild_frontierComplete hrightPending
            (Fin.cast (by simp) mate) rightMateEdge hright)
      rw [toDiag_connect st hcomplete hpending mate hmate hstep]
      rw [toDiag_connect right hright hrightPending
        (Fin.cast (by simp) mate) rightMateEdge hrightStep]
      have hidx := hrel.restLabelIndex hpending mate
      cases hidx
      have hok :
          right.connect_compatible hrightPending (Fin.cast (by simp) mate)
              rightMateEdge =
            st.connect_compatible hpending mate hmate := Subsingleton.elim _ _
      cases hok
      exact congrArg (fun child => Diag.connect
        (st.restLabelIndex hpending mate)
        (st.connect_compatible hpending mate hmate) child) hchild
  | case3 activeLabel restLabels active rest node slot hmate st _hcomplete
      hcomplete hpending hunseen hstep _hstep ih =>
      have hconnect :=
        st.firstPendingConnectSearch?_none_of_firstPendingStepSearch?_bud hstep
      have hrightPending := hrel.pending_cons hpending
      rcases hrel.firstPendingStepSearch?_bud hpending hconnect node slot
          hmate hunseen with
        ⟨rightMateEdge, rightUnseen, hrightStep⟩
      let rightNode := e.nodeEquiv.toFun node
      let rightSlot := PortHypergraphIso.incidenceSlotPreserved e node slot
      have rightUnseenMem : rightNode ∉ right.seenNodes := by
        simpa [rightNode, seenNode] using rightUnseen
      have leftUnseenMem : node ∉ st.seenNodes := by
        simpa [seenNode] using hunseen
      have hfrontier :
          restLabels ++
              Sig.nodePortsExcept (H.raw.nodeLabel rightNode)
                (budEntry (G := H) rightNode rightSlot) =
            restLabels ++
              Sig.nodePortsExcept (G.raw.nodeLabel node)
                (budEntry (G := G) node slot) := by
        have hentryVal := budEntry_val_preserved e node slot
        exact congrArg (fun tail => restLabels ++ tail)
          (nodePortsExcept_eq_of_val
            (e.node_label_preserved node).symm hentryVal)
      let rightChild :=
        hfrontier ▸
          right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem
      have hchildRel :
          IsoRelated e
            (st.budChild hpending node slot hmate leftUnseenMem)
            rightChild := by
        dsimp [rightChild, rightNode, rightSlot, hfrontier]
        exact hrel.budChild_with hpending node slot hmate leftUnseenMem
          rightMateEdge rightUnseenMem
      have hrightChildCompleteUncast :
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem).FrontierComplete :=
        right.budChild_frontierComplete hrightPending rightNode rightSlot
          rightMateEdge rightUnseenMem hright
      have hrightChildComplete : rightChild.FrontierComplete := by
        dsimp [rightChild]
        exact frontierComplete_cast hfrontier
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem)
          hrightChildCompleteUncast
      have hchild := ih rightChild hchildRel hrightChildComplete
      rw [toDiag_bud st hcomplete hpending node slot hmate hunseen hstep]
      rw [toDiag_bud right hright hrightPending rightNode rightSlot
        rightMateEdge rightUnseen hrightStep]
      have hrightChildDiagCast :
          rightChild.toDiag hrightChildComplete =
            hfrontier ▸
              (right.budChild hrightPending rightNode rightSlot rightMateEdge
                rightUnseenMem).toDiag hrightChildCompleteUncast := by
        dsimp [rightChild, hrightChildComplete]
        exact toDiag_cast hfrontier
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem)
          hrightChildCompleteUncast
      have hchildCast :
          (st.budChild hpending node slot hmate leftUnseenMem).toDiag
              (st.budChild_frontierComplete hpending node slot hmate
                leftUnseenMem hcomplete) =
            hfrontier ▸
              (right.budChild hrightPending rightNode rightSlot rightMateEdge
                rightUnseenMem).toDiag hrightChildCompleteUncast := by
        exact hchild.trans hrightChildDiagCast
      exact Diag.bud_transport
        (hnode := (e.node_label_preserved node).symm)
        (hentryVal := budEntry_val_preserved e node slot)
        (okA := st.bud_compatible hpending node slot hmate)
        (okB := right.bud_compatible hrightPending rightNode rightSlot
          rightMateEdge)
        (childA :=
          (st.budChild hpending node slot hmate leftUnseenMem).toDiag
            (st.budChild_frontierComplete hpending node slot hmate
              leftUnseenMem hcomplete))
        (childB :=
          (right.budChild hrightPending rightNode rightSlot rightMateEdge
            rightUnseenMem).toDiag hrightChildCompleteUncast)
        hfrontier hchildCast

end SearchState

def fromGraph (G : OpenPortHypergraph Sig boundary) : Diag Sig boundary :=
  (SearchState.initial G).toDiag (SearchState.initial_frontierComplete G)

namespace SearchState

/-- Semantic exhaustion for a finite search state: all constructors have been
seen and all edges have been consumed by traversal steps. -/
structure GraphExhausted {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier) : Prop where
  allNodesSeen : ∀ node : Fin G.raw.nodeCount, node ∈ st.seenNodes
  allEdgesProcessed : ∀ edge : Fin G.raw.edgeCount, edge ∈ st.processedEdges

theorem pending_ne_nil_of_reachable_unprocessed
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    {endpoint : Fin G.raw.endpointCount}
    (hreach : PortHypergraph.PortReachesBoundary G.raw endpoint)
    (hunprocessed : G.raw.endpointEdge endpoint ∉ st.processedEdges) :
    st.pending ≠ [] := by
  induction hreach with
  | boundary b =>
      intro hpendingNil
      have hmem :
          G.raw.boundaryPort b ∈ st.pending :=
        hcomplete (G.raw.boundaryPort b) hunprocessed (.boundary b) rfl
      rw [hpendingNil] at hmem
      cases hmem
  | throughEdge sameEdge _different _reach ih =>
      apply ih
      intro hprocessed
      exact hunprocessed (by
        rw [← sameEdge]
        exact hprocessed)
  | throughConstructor node fromSlot toSlot hp hq _reach ih =>
      by_cases hseen : node ∈ st.seenNodes
      · intro hpendingNil
        have htoUnprocessed :
            G.raw.endpointEdge ((G.raw.incident node).get toSlot) ∉
              st.processedEdges := by
          rw [hq]
          exact hunprocessed
        have hmem :
            (G.raw.incident node).get toSlot ∈ st.pending :=
          hcomplete ((G.raw.incident node).get toSlot) htoUnprocessed
            (.constructor node toSlot) rfl hseen
        rw [hpendingNil] at hmem
        cases hmem
      · have hfromUnprocessed :
            G.raw.endpointEdge ((G.raw.incident node).get fromSlot) ∉
              st.processedEdges :=
          st.unseen_incident_unprocessed node hseen fromSlot
        apply ih
        rw [← hp]
        exact hfromUnprocessed

theorem allNodesSeen_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    ∀ node : Fin G.raw.nodeCount, node ∈ st.seenNodes := by
  intro node
  by_cases hseen : node ∈ st.seenNodes
  · exact hseen
  · rcases G.allConstructorsReachBoundary node with ⟨slot, hreach⟩
    have hunprocessed :
        G.raw.endpointEdge ((G.raw.incident node).get slot) ∉
          st.processedEdges :=
      st.unseen_incident_unprocessed node hseen slot
    have hnonempty :=
      st.pending_ne_nil_of_reachable_unprocessed hcomplete hreach hunprocessed
    exact False.elim (hnonempty hpendingNil)

theorem allEdgesProcessed_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    ∀ edge : Fin G.raw.edgeCount, edge ∈ st.processedEdges := by
  intro edge
  by_cases hprocessed : edge ∈ st.processedEdges
  · exact hprocessed
  · rcases G.raw.edge_two_endpoints edge with
      ⟨left, _right, _hdiff, hleft, _hright, _hall⟩
    have hleftUnprocessed :
        G.raw.endpointEdge left ∉ st.processedEdges := by
      intro hleftProcessed
      exact hprocessed (by simpa [hleft] using hleftProcessed)
    rcases G.raw.endpoint_owner left with ⟨owner, howner, _huniq⟩
    cases owner with
    | boundary boundaryIndex =>
        have hownerEndpoint :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.boundary boundaryIndex) = left := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hmem :
            left ∈ st.pending :=
          hcomplete left hleftUnprocessed (.boundary boundaryIndex)
            hownerEndpoint
        rw [hpendingNil] at hmem
        cases hmem
    | constructor node slot =>
        have hownerEndpoint :
            PortHypergraph.endpointOwnerEndpoint G.raw
                (.constructor node slot) = left := by
          simpa [PortHypergraph.endpointOwnerEndpoint] using howner
        have hseen : node ∈ st.seenNodes :=
          st.allNodesSeen_of_pending_nil hcomplete hpendingNil node
        have hmem :
            left ∈ st.pending :=
          hcomplete left hleftUnprocessed (.constructor node slot)
            hownerEndpoint hseen
        rw [hpendingNil] at hmem
        cases hmem

theorem graphExhausted_of_pending_nil
    {G : OpenPortHypergraph Sig boundary}
    {frontier : List Sig.Port} (st : SearchState G frontier)
    (hcomplete : st.FrontierComplete)
    (hpendingNil : st.pending = []) :
    st.GraphExhausted where
  allNodesSeen := st.allNodesSeen_of_pending_nil hcomplete hpendingNil
  allEdgesProcessed := st.allEdgesProcessed_of_pending_nil hcomplete hpendingNil

theorem pending_eq_nil_of_empty_frontier
    {G : OpenPortHypergraph Sig boundary} (st : SearchState G []) :
    st.pending = [] := by
  cases hpending : st.pending with
  | nil => rfl
  | cons active rest =>
      have hlabels := st.pending_labels
      rw [hpending] at hlabels
      simp at hlabels

theorem graphExhausted_of_empty_frontier
    {G : OpenPortHypergraph Sig boundary} (st : SearchState G [])
    (hcomplete : st.FrontierComplete) :
    st.GraphExhausted :=
  st.graphExhausted_of_pending_nil hcomplete
    st.pending_eq_nil_of_empty_frontier

end SearchState

def isoRel (G H : OpenPortHypergraph Sig boundary) : Prop :=
  Nonempty (PortHypergraphIso G.raw H.raw)

def isoSetoid (Sig : Signature) (boundary : List Sig.Port) :
    Setoid (OpenPortHypergraph Sig boundary) where
  r := isoRel
  iseqv := by
    constructor
    · intro G
      exact ⟨PortHypergraphIso.refl G.raw⟩
    · intro G H h
      rcases h with ⟨e⟩
      exact ⟨PortHypergraphIso.symm e⟩
    · intro G H K hGH hHK
      rcases hGH with ⟨eGH⟩
      rcases hHK with ⟨eHK⟩
      exact ⟨PortHypergraphIso.trans eGH eHK⟩

end OpenPortHypergraph

namespace Diag

variable {Sig : Signature}

/--
Bridge support for the syntax round-trip: in the semantic graph rendered from
a top-level `connect`, the executable first-pending search on the initial
ordered-boundary state returns the corresponding `connect` branch.
-/
theorem toOpenPortHypergraph_connect_initial_search
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate)) :
    let d : Diag Sig (active :: frontier) := Diag.connect mate ok child
    let G := Diag.toOpenPortHypergraph d
    let st := OpenPortHypergraph.SearchState.initial G
    let rest : List (Fin G.raw.endpointCount) :=
      List.ofFn fun i : Fin frontier.length =>
        G.raw.boundaryPort ⟨i.val + 1, by
          simp [i.isLt]⟩
    ∃ hmate : PortHypergraph.EdgeMate G.raw
        (G.raw.boundaryPort ⟨0, by simp⟩)
        (rest.get (Fin.cast (by dsimp [rest]; simp) mate)),
      st.firstPendingStepSearch?
          (G.raw.boundaryPort ⟨0, by simp⟩) rest =
        some (OpenPortHypergraph.FirstPendingStep.connect
          (Fin.cast (by dsimp [rest]; simp) mate) hmate) := by
  intro d G st rest
  let mateTail : Fin rest.length := Fin.cast (by simp [rest]) mate
  have hpending :
      st.pending = G.raw.boundaryPort ⟨0, by simp⟩ :: rest := by
    dsimp [st, OpenPortHypergraph.SearchState.initial, rest]
    rw [List.ofFn_succ]
    congr
  have hrestGet :
      rest.get mateTail =
        G.raw.boundaryPort ⟨mate.val + 1, by
          simp [mate.isLt]⟩ := by
    simp [rest, mateTail]
  have hmateBase :=
    Diag.toOpenPortHypergraph_connect_boundary_edgeMate mate ok child
  have hmate :
      PortHypergraph.EdgeMate G.raw
        (G.raw.boundaryPort ⟨0, by simp⟩)
        (rest.get mateTail) := by
    rw [hrestGet]
    simpa [d, G] using hmateBase
  have hrestNodup := st.rest_nodup hpending
  rcases st.firstPendingStepSearch?_some_connect_exact_of_witness
      hrestNodup mateTail hmate with ⟨hmate', hstep⟩
  refine ⟨hmate', ?_⟩
  simpa [mateTail] using hstep

/--
Bridge support for the syntax round-trip: in the semantic graph rendered from
a top-level `bud`, the executable first-pending search on the initial
ordered-boundary state returns the corresponding `bud` branch.  The proof also
shows that no pending-boundary `connect` mate can precede the constructor entry,
using endpoint-owner uniqueness to separate boundary endpoints from constructor
incidences.
-/
theorem toOpenPortHypergraph_bud_initial_search
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry)) :
    let d : Diag Sig (active :: frontier) := Diag.bud node entry ok child
    let G := Diag.toOpenPortHypergraph d
    let st := OpenPortHypergraph.SearchState.initial G
    let rest : List (Fin G.raw.endpointCount) :=
      List.ofFn fun i : Fin frontier.length =>
        G.raw.boundaryPort ⟨i.val + 1, by
          simp [i.isLt]⟩
    ∃ (nodeIndex : Fin G.raw.nodeCount)
      (slot : Fin (G.raw.incident nodeIndex).length)
      (hmate : PortHypergraph.EdgeMate G.raw
        (G.raw.boundaryPort ⟨0, by simp⟩)
        ((G.raw.incident nodeIndex).get slot))
      (hunseen : ¬ st.seenNode nodeIndex),
      st.firstPendingStepSearch?
          (G.raw.boundaryPort ⟨0, by simp⟩) rest =
        some (OpenPortHypergraph.FirstPendingStep.bud
          nodeIndex slot hmate hunseen) := by
  intro d G st rest
  rcases Diag.toOpenPortHypergraph_bud_boundary_entry_edgeMate
      node entry ok child with
    ⟨nodeIndex, slot, _hnodeLabel, _hslotVal, hmate⟩
  have hunseen : ¬ st.seenNode nodeIndex := by
    simp [st, OpenPortHypergraph.SearchState.initial,
      OpenPortHypergraph.SearchState.seenNode]
  have hboundary_constructor_ne
      (b : Fin (active :: frontier).length) :
      G.raw.boundaryPort b ≠ (G.raw.incident nodeIndex).get slot := by
    intro hsame
    let endpoint := G.raw.boundaryPort b
    rcases G.raw.endpoint_owner endpoint with ⟨owner₀, _howner₀, huniq⟩
    have hboundaryEq :
        (.boundary b :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      rfl
    have hconstructorEq :
        (.constructor nodeIndex slot :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) = owner₀ := by
      apply huniq
      change (G.raw.incident nodeIndex).get slot = endpoint
      exact hsame.symm
    have himpossible :
        (.boundary b :
          EndpointOwner (active :: frontier).length G.raw.nodeCount
            (fun node => (G.raw.incident node).length)) =
        .constructor nodeIndex slot :=
      hboundaryEq.trans hconstructorEq.symm
    cases himpossible
  have hconnect :
      OpenPortHypergraph.firstPendingConnectSearch? G st.seenNode
        (G.raw.boundaryPort ⟨0, by simp⟩) rest = none := by
    cases hcase :
        OpenPortHypergraph.firstPendingConnectSearch? G st.seenNode
          (G.raw.boundaryPort ⟨0, by simp⟩) rest with
    | none => rfl
    | some step =>
        rcases OpenPortHypergraph.firstPendingConnectSearch?_some_connect
            G st.seenNode hcase with ⟨tailMate, htailMate, _hstep⟩
        have hsameMate :
            rest.get tailMate = (G.raw.incident nodeIndex).get slot := by
          rcases PortHypergraph.edgeMate_existsUnique G.raw
              (G.raw.boundaryPort ⟨0, by simp⟩) with
            ⟨uniqueMate, _huniqueMate, huniq⟩
          exact (huniq (rest.get tailMate) htailMate).trans
            (huniq ((G.raw.incident nodeIndex).get slot) hmate).symm
        let b : Fin (active :: frontier).length :=
          ⟨tailMate.val + 1, by
            have htail := tailMate.isLt
            simp [rest] at htail
            simp
            omega⟩
        have hrestBoundary :
            rest.get tailMate = G.raw.boundaryPort b := by
          simp [rest, b]
        exact False.elim
          (hboundary_constructor_ne b (hrestBoundary.symm.trans hsameMate))
  rcases st.firstPendingStepSearch?_some_bud_exact_of_witness
      hconnect nodeIndex slot hmate hunseen with
    ⟨hmate', hunseen', hstep⟩
  exact ⟨nodeIndex, slot, hmate', hunseen', hstep⟩

/--
Arbitrary-prefix version of rendered `connect` recognition.  If a completed
render trace is viewed through semantic graph evidence, the edge introduced by
the current top-level `connect` makes the active frontier endpoint and selected
mate endpoint edge-mates in that semantic graph.
-/
theorem renderTrace_connect_edgeMate_of_invariants
    {active : Sig.Port} {frontier : List Sig.Port}
    (mate : Fin frontier.length)
    (ok : Sig.compatible active (frontier.get mate))
    (child : Diag Sig (eraseFin frontier mate))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hv : (renderTrace (Diag.connect mate ok child) st).ValidIds)
    (hp : (renderTrace (Diag.connect mate ok child) st).EndpointPartition)
    (hn : (renderTrace (Diag.connect mate ok child) st).NodeIncidentNodup)
    (pref :
      (renderTrace (Diag.connect mate ok child) st).EndpointPrefix boundary)
    (ho :
      (renderTrace (Diag.connect mate ok child) st).OwnerIdPartition boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.connect mate ok child) st
    let G :=
      (RenderState.portHypergraphEvidenceOfInvariants
        hv hp hn pref ho).toPortHypergraph
    let mateId :=
      restIds.get (Fin.cast (by
        have hlen := st.frontierIds_length
        rw [hids] at hlen
        exact (Nat.succ.inj hlen).symm) mate)
    ∃ (hactive : activeId < final.endpoints.length)
      (hmateBound : mateId < final.endpoints.length),
      PortHypergraph.EdgeMate G
        ⟨activeId, hactive⟩ ⟨mateId, hmateBound⟩ := by
  intro final G mateId
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := frontier.get mate
      left := activeId
      right := mateId
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  have hedgeMem : edge ∈ final.edges := by
    simpa [final, edge, mateId] using
      renderTrace_connect_edge_mem mate ok child st hids
  rcases list_exists_get_of_mem final.edges hedgeMem with
    ⟨edgeIndex, hedgeIndex⟩
  have hleftEq : (final.edges.get edgeIndex).left = activeId := by
    have h := congrArg RenderEdge.left hedgeIndex
    simpa [edge] using h
  have hrightEq : (final.edges.get edgeIndex).right = mateId := by
    have h := congrArg RenderEdge.right hedgeIndex
    simpa [edge] using h
  have hleftEqRaw :
      (((renderTrace (Diag.connect mate ok child) st).edges.get edgeIndex).left) =
        activeId := by
    simpa [final] using hleftEq
  have hrightEqRaw :
      (((renderTrace (Diag.connect mate ok child) st).edges.get edgeIndex).right) =
        mateId := by
    simpa [final] using hrightEq
  have hactiveBound :
      activeId < final.endpoints.length := by
    have h := hv.edge_left_bound (final.edges.get edgeIndex)
      (List.get_mem final.edges edgeIndex)
    rw [hleftEqRaw] at h
    simpa [final] using h
  have hmateBound :
      mateId < final.endpoints.length := by
    have h := hv.edge_right_bound (final.edges.get edgeIndex)
      (List.get_mem final.edges edgeIndex)
    rw [hrightEqRaw] at h
    simpa [final] using h
  refine ⟨hactiveBound, hmateBound, ?_⟩
  have hactiveVal :
      (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val =
        (final.edges.get edgeIndex).left :=
    hleftEq.symm
  have hmateVal :
      (⟨mateId, hmateBound⟩ : Fin final.endpoints.length).val =
        (final.edges.get edgeIndex).right :=
    hrightEq.symm
  constructor
  · intro hsame
    have hval := congrArg (fun endpoint => endpoint.val) hsame
    have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
    exact hne (by
      calc
        (final.edges.get edgeIndex).left =
            (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val :=
          hactiveVal.symm
        _ = (⟨mateId, hmateBound⟩ : Fin final.endpoints.length).val := hval
        _ = (final.edges.get edgeIndex).right := hmateVal)
  · have hleft :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
        edgeIndex (Or.inl hactiveVal)
    have hright :=
      RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
        (⟨mateId, hmateBound⟩ : Fin final.endpoints.length)
        edgeIndex (Or.inr hmateVal)
    simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants,
      RenderState.edgeEvidenceOfPartition,
      RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

/--
Arbitrary-prefix version of rendered `bud` recognition.  If a completed render
trace is viewed through semantic graph evidence, the constructor introduced by
the current top-level `bud` has the original label and entry position, and the
active frontier endpoint is edge-mated to that constructor entry endpoint.
-/
theorem renderTrace_bud_entry_edgeMate_of_invariants
    {active : Sig.Port} {frontier : List Sig.Port}
    (node : Sig.Node)
    (entry : Fin (Sig.arity node))
    (ok : Sig.compatible active (Sig.port node entry))
    (child : Diag Sig (frontier ++ Sig.nodePortsExcept node entry))
    (st : RenderState Sig (active :: frontier))
    {boundary : List Sig.Port}
    (hv : (renderTrace (Diag.bud node entry ok child) st).ValidIds)
    (hp : (renderTrace (Diag.bud node entry ok child) st).EndpointPartition)
    (hn : (renderTrace (Diag.bud node entry ok child) st).NodeIncidentNodup)
    (pref :
      (renderTrace (Diag.bud node entry ok child) st).EndpointPrefix boundary)
    (ho :
      (renderTrace (Diag.bud node entry ok child) st).OwnerIdPartition boundary)
    {activeId : Nat} {restIds : List Nat}
    (hids : st.frontierIds = activeId :: restIds) :
    let final := renderTrace (Diag.bud node entry ok child) st
    let G :=
      (RenderState.portHypergraphEvidenceOfInvariants
        hv hp hn pref ho).toPortHypergraph
    ∃ (hactive : activeId < final.endpoints.length)
      (nodeIndex : Fin G.nodeCount)
      (slot : Fin (G.incident nodeIndex).length),
      G.nodeLabel nodeIndex = node ∧
        slot.val = entry.val ∧
        PortHypergraph.EdgeMate G
          ⟨activeId, hactive⟩ ((G.incident nodeIndex).get slot) := by
  intro final G
  let nodeEndpoints := freshNodeEndpoints st.nextEndpoint (Sig.arity node)
  let entryIdx : Fin nodeEndpoints.length :=
    Fin.cast (by simp [nodeEndpoints]) entry
  let edge : RenderEdge Sig :=
    { label := Sig.portEdge active
      leftLabel := active
      rightLabel := Sig.port node entry
      left := activeId
      right := nodeEndpoints.get entryIdx
      left_label := rfl
      right_label := (Sig.compatible_edge ok).symm
      compatible := ok }
  let renderNode : RenderNode Sig :=
    { label := node
      incident := nodeEndpoints }
  have hedgeMem : edge ∈ final.edges := by
    simpa [final, edge, nodeEndpoints, entryIdx] using
      renderTrace_bud_edge_mem node entry ok child st hids
  have hnodeMem : renderNode ∈ final.nodes := by
    simpa [final, renderNode, nodeEndpoints] using
      renderTrace_bud_node_mem node entry ok child st
  rcases list_exists_get_of_mem final.edges hedgeMem with
    ⟨edgeIndex, hedgeIndex⟩
  rcases list_exists_get_of_mem final.nodes hnodeMem with
    ⟨nodeIndex, hnodeIndex⟩
  have hleftEq : (final.edges.get edgeIndex).left = activeId := by
    have h := congrArg RenderEdge.left hedgeIndex
    simpa [edge] using h
  have hrightEq :
      (final.edges.get edgeIndex).right = nodeEndpoints.get entryIdx := by
    have h := congrArg RenderEdge.right hedgeIndex
    simpa [edge] using h
  have hleftEqRaw :
      (((renderTrace (Diag.bud node entry ok child) st).edges.get edgeIndex).left) =
        activeId := by
    simpa [final] using hleftEq
  have hactiveBound :
      activeId < final.endpoints.length := by
    have h := hv.edge_left_bound (final.edges.get edgeIndex)
      (List.get_mem final.edges edgeIndex)
    rw [hleftEqRaw] at h
    simpa [final] using h
  have hnodeLabel : G.nodeLabel nodeIndex = node := by
    dsimp [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
      RenderState.portHypergraphEvidenceOfInvariants, renderNode,
      nodeEndpoints] at *
    rw [hnodeIndex]
  let slot : Fin (G.incident nodeIndex).length :=
    Fin.cast (by
      calc
        Sig.arity node = Sig.arity (G.nodeLabel nodeIndex) := by
          rw [hnodeLabel]
        _ = (G.incident nodeIndex).length :=
          (G.incident_length nodeIndex).symm) entry
  refine ⟨hactiveBound, nodeIndex, slot, hnodeLabel, ?_, ?_⟩
  · simp [slot]
  · have hincidentVal :
        ((G.incident nodeIndex).get slot).val =
          (final.edges.get edgeIndex).right := by
      have hincidentList :
          (final.nodes.get nodeIndex).incident = nodeEndpoints := by
        simpa [renderNode] using congrArg RenderNode.incident hnodeIndex
      have hentryGet :
          (final.nodes.get nodeIndex).incident.get
              (Fin.cast (by
                rw [hincidentList]
                simp [nodeEndpoints]) entry) =
            nodeEndpoints.get entryIdx := by
        have hleftBound :
            entry.val < (final.nodes.get nodeIndex).incident.length := by
          rw [hincidentList]
          simp [nodeEndpoints]
        have hrightBound : entry.val < nodeEndpoints.length := by
          simp [nodeEndpoints]
        have hleftIdx :
            (Fin.cast (by
              rw [hincidentList]
              simp [nodeEndpoints]) entry :
                Fin (final.nodes.get nodeIndex).incident.length) =
              ⟨entry.val, hleftBound⟩ := by
          apply Fin.ext
          rfl
        have hrightIdx : entryIdx = ⟨entry.val, hrightBound⟩ := by
          apply Fin.ext
          rfl
        have hopt :
            (final.nodes.get nodeIndex).incident[entry.val]? =
              nodeEndpoints[entry.val]? := by
          rw [hincidentList]
        have hleftSome :
            (final.nodes.get nodeIndex).incident[entry.val]? =
              some ((final.nodes.get nodeIndex).incident.get
                ⟨entry.val, hleftBound⟩) :=
          List.getElem?_eq_getElem hleftBound
        have hrightSome :
            nodeEndpoints[entry.val]? =
              some (nodeEndpoints.get ⟨entry.val, hrightBound⟩) :=
          List.getElem?_eq_getElem hrightBound
        have hget :
            (final.nodes.get nodeIndex).incident.get ⟨entry.val, hleftBound⟩ =
              nodeEndpoints.get ⟨entry.val, hrightBound⟩ := by
          rw [hleftSome, hrightSome] at hopt
          injection hopt with hget
        rw [hleftIdx, hrightIdx]
        exact hget
      dsimp [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.incidenceEvidenceOfValidIds,
        RenderState.incidentOfValidIds, edge, slot, renderNode,
        nodeEndpoints, entryIdx]
      simpa [entryIdx] using hentryGet.trans hrightEq.symm
    constructor
    · intro hsame
      have hval := congrArg (fun endpoint => endpoint.val) hsame
      have hne := RenderState.edge_left_ne_right_of_partition hp edgeIndex
      exact hne (by
        calc
          (final.edges.get edgeIndex).left =
              (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length).val :=
            hleftEq
          _ = ((G.incident nodeIndex).get slot).val := hval
          _ = (final.edges.get edgeIndex).right := hincidentVal)
    · have hleft :=
        RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
          (⟨activeId, hactiveBound⟩ : Fin final.endpoints.length)
          edgeIndex (Or.inl hleftEqRaw.symm)
      have hright :=
        RenderState.endpointEdgeOfPartition_eq_of_endpoint_side hp
          ((G.incident nodeIndex).get slot) edgeIndex (Or.inr hincidentVal)
      simpa [G, RenderState.PortHypergraphEvidence.toPortHypergraph,
        RenderState.portHypergraphEvidenceOfInvariants,
        RenderState.edgeEvidenceOfPartition,
        RenderState.endpointEdgeEvidenceOfPartition] using hleft.trans hright.symm

end Diag

/-- Typed open boundary-connected port-hypergraphs quotiented by ordered
boundary-preserving isomorphism. -/
def OpenPortHypergraphUpToIso (Sig : Signature) (boundary : List Sig.Port) :
    Type :=
  Quotient (OpenPortHypergraph.isoSetoid Sig boundary)

/--
The owned graph-to-`Diag` traversal is invariant under
ordered-boundary-preserving isomorphism.  This is the well-definedness
theorem for descending `OpenPortHypergraph.fromGraph` to
`OpenPortHypergraphUpToIso`.
-/
theorem OpenPortHypergraph.fromGraph_respects_iso
    {Sig : Signature} {boundary : List Sig.Port}
    {G H : OpenPortHypergraph Sig boundary}
    (h : OpenPortHypergraph.isoRel G H) :
    OpenPortHypergraph.fromGraph G = OpenPortHypergraph.fromGraph H := by
  rcases h with ⟨e⟩
  simpa [OpenPortHypergraph.fromGraph] using
    SearchState.toDiag_isoRelated e
      (SearchState.initial G) (SearchState.initial H)
      (SearchState.initial_isoRelated e)
      (SearchState.initial_frontierComplete G)
      (SearchState.initial_frontierComplete H)

/--
UNFINISHED inverse law: rendering a syntax diagram to a semantic graph and then
running the owned first-pending traversal recovers the original syntax exactly.
-/
theorem Diag.fromGraph_toOpenPortHypergraph
    {Sig : Signature} {boundary : List Sig.Port}
    (d : Diag Sig boundary) :
    OpenPortHypergraph.fromGraph (Diag.toOpenPortHypergraph d) = d := by
  sorry

/--
UNFINISHED inverse law: traversing an open graph to syntax and rendering that
syntax gives an ordered-boundary-preserving isomorphic semantic graph.
-/
theorem OpenPortHypergraph.toOpenPortHypergraph_fromGraph_iso
    {Sig : Signature} {boundary : List Sig.Port}
    (G : OpenPortHypergraph Sig boundary) :
    OpenPortHypergraph.isoRel
      (Diag.toOpenPortHypergraph (OpenPortHypergraph.fromGraph G)) G := by
  sorry

/--
UNFINISHED semantic bridge assembly.  The quotient maps are now wired through
the owned renderer and traversal, but this declaration still depends on the
two unfinished inverse-law declarations above.
-/
def diagOpenPortHypergraphIso (Sig : Signature) (boundary : List Sig.Port) :
    Diag Sig boundary ≃ᵢ OpenPortHypergraphUpToIso Sig boundary where
  toFun d :=
    Quotient.mk (OpenPortHypergraph.isoSetoid Sig boundary)
      (Diag.toOpenPortHypergraph d)
  invFun :=
    Quotient.lift
      (fun G : OpenPortHypergraph Sig boundary => OpenPortHypergraph.fromGraph G)
      (by
        intro G H h
        exact OpenPortHypergraph.fromGraph_respects_iso h)
  left_inv := by
    intro d
    exact Diag.fromGraph_toOpenPortHypergraph d
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro G
    exact Quotient.sound
      (OpenPortHypergraph.toOpenPortHypergraph_fromGraph_iso G)

end StringDiagram
end BijForm
