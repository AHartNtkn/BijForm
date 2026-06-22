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

theorem eraseFin_length_eq_of_length_eq {α β : Type}
    {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length)
    (ix : Fin xs.length) (iy : Fin ys.length) :
    (eraseFin xs ix).length = (eraseFin ys iy).length := by
  simp [eraseFin_length, hlen]

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

theorem list_get_of_eq_append_left {α : Type}
    {full pref suffix : List α}
    (hfull : full = pref ++ suffix)
    (i : Fin full.length) (hi : i.val < pref.length) :
    full.get i = pref.get ⟨i.val, hi⟩ := by
  subst full
  exact list_get_append_left pref suffix hi i.isLt

theorem list_get_of_eq_append_right {α : Type}
    {full pref suffix : List α}
    (hfull : full = pref ++ suffix)
    (i : Fin full.length) (hi : pref.length ≤ i.val) :
    full.get i =
      suffix.get ⟨i.val - pref.length, by
        subst full
        have hlen : (pref ++ suffix).length = pref.length + suffix.length := by
          simp
        omega⟩ := by
  subst full
  exact list_get_append_right pref suffix hi i.isLt

theorem list_get_append_single_at_length {α : Type}
    (xs ys : List α) (x : α) :
    (xs ++ x :: ys).get ⟨xs.length, by simp⟩ = x := by
  change (xs ++ x :: ys)[xs.length] = x
  simp

theorem list_get_of_eq_append_cons_at_length {α : Type}
    {full pref suffix : List α} {x : α}
    (hfull : full = pref ++ x :: suffix)
    (i : Fin full.length) (hval : i.val = pref.length) :
    full.get i = x := by
  subst full
  have hidx :
      i = ⟨pref.length, by
        simp⟩ := by
    apply Fin.ext
    exact hval
  rw [hidx]
  exact list_get_append_single_at_length pref suffix x

theorem list_get_of_eq {α : Type} {xs ys : List α}
    (h : xs = ys) (i : Fin xs.length) :
    xs.get i = ys.get (Fin.cast (congrArg List.length h) i) := by
  cases h
  rfl

theorem list_get_of_eq_of_val_eq {α : Type} {xs ys : List α}
    (h : xs = ys) (i : Fin xs.length) (j : Fin ys.length)
    (hval : i.val = j.val) :
    xs.get i = ys.get j := by
  have hget := list_get_of_eq h i
  have hidx :
      Fin.cast (congrArg List.length h) i = j := by
    apply Fin.ext
    exact hval
  simpa [hidx] using hget

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

theorem list_get_map_eq_get {α β : Type} (f : α → β)
    {xs : List α} {ys : List β}
    (hmap : xs.map f = ys) (i : Fin xs.length) :
    f (xs.get i) =
      ys.get (Fin.cast (by rw [← hmap]; simp) i) := by
  cases hmap
  simp

theorem list_get_map_eq_get_of_val_eq {α β : Type} (f : α → β)
    {xs : List α} {ys : List β}
    (hmap : xs.map f = ys) (i : Fin xs.length) (j : Fin ys.length)
    (hval : i.val = j.val) :
    f (xs.get i) = ys.get j := by
  have hget := list_get_map_eq_get f hmap i
  have hidx :
      (Fin.cast (by rw [← hmap]; simp) i : Fin ys.length) = j := by
    apply Fin.ext
    exact hval
  simpa [hidx] using hget

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

theorem list_nodup_reverse {α : Type} {xs : List α}
    (hnodup : xs.Nodup) : xs.reverse.Nodup := by
  change List.Pairwise (fun left right : α => left ≠ right) xs.reverse
  rw [List.pairwise_reverse]
  change List.Pairwise (fun left right : α => right ≠ left) xs
  exact hnodup.imp (by
    intro left right hne
    exact hne.symm)

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

def listIndexOfMem {α : Type} [DecidableEq α] :
    (xs : List α) → (x : α) → x ∈ xs → Fin xs.length
  | [], _x, hmem => False.elim (by cases hmem)
  | y :: ys, x, hmem =>
      if hxy : x = y then
        ⟨0, by simp⟩
      else
        let htail : x ∈ ys := by
          simp at hmem
          rcases hmem with hhead | htail
          · exact False.elim (hxy hhead)
          · exact htail
        let idx := listIndexOfMem ys x htail
        ⟨idx.val + 1, by simp [idx.isLt]⟩

theorem listIndexOfMem_get {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (x : α) (hmem : x ∈ xs),
      xs.get (listIndexOfMem xs x hmem) = x
  | [], _x, hmem => by cases hmem
  | y :: ys, x, hmem => by
      unfold listIndexOfMem
      by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy]
        let htail : x ∈ ys := by
          simp at hmem
          rcases hmem with hhead | htail
          · exact False.elim (hxy hhead)
          · exact htail
        exact listIndexOfMem_get ys x htail

theorem listIndexOfMem_get_eq_of_nodup {α : Type} [DecidableEq α] :
    ∀ (xs : List α), xs.Nodup → (i : Fin xs.length) →
      listIndexOfMem xs (xs.get i) (List.get_mem xs i) = i
  | [], _hnodup, i => by
      cases i with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | y :: ys, hnodup, i => by
      cases i with
      | mk iVal iLt =>
          cases iVal with
          | zero =>
              unfold listIndexOfMem
              simp
          | succ iVal =>
              have hsplit : y ∉ ys ∧ ys.Nodup := by
                simpa using hnodup
              let tailIndex : Fin ys.length :=
                ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩
              have hne : ys.get tailIndex ≠ y := by
                intro hsame
                exact hsplit.1 (by
                  rw [← hsame]
                  exact List.get_mem ys tailIndex)
              have htailBound : iVal < ys.length :=
                Nat.lt_of_succ_lt_succ iLt
              have hneVal : ¬ ys[iVal]'htailBound = y := by
                intro hsame
                exact hne (by
                  simpa [tailIndex] using hsame)
              unfold listIndexOfMem
              simp [hneVal]
              have hrec :=
                congrArg Fin.val
                  (listIndexOfMem_get_eq_of_nodup ys hsplit.2 tailIndex)
              simpa [tailIndex] using hrec

def finCastIso {m n : Nat} (h : m = n) : Fin m ≃ᵢ Fin n where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by
    intro x
    cases h
    rfl
  right_inv := by
    intro x
    cases h
    rfl

theorem fin_mk_val_eq {n : Nat} (i : Fin n) (h : i.val < n) :
    (⟨i.val, h⟩ : Fin n) = i := by
  apply Fin.ext
  rfl

theorem fin_eq_of_val_eq {n : Nat} {i j : Fin n} (h : i.val = j.val) :
    i = j := by
  apply Fin.ext
  exact h

def listFinIso {n : Nat} (xs : List (Fin n))
    (hnodup : xs.Nodup)
    (hcover : ∀ x : Fin n, x ∈ xs) :
    Fin xs.length ≃ᵢ Fin n where
  toFun i := xs.get i
  invFun x := listIndexOfMem xs x (hcover x)
  left_inv := by
    intro i
    exact listIndexOfMem_get_eq_of_nodup xs hnodup i
  right_inv := by
    intro x
    exact listIndexOfMem_get xs x (hcover x)

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

theorem list_length_eq_fin_of_nodup_cover {n : Nat}
    (xs : List (Fin n)) (hnodup : xs.Nodup)
    (hcover : ∀ x : Fin n, x ∈ xs) :
    xs.length = n := by
  have hle : xs.length ≤ n :=
    list_length_le_fin_of_nodup xs hnodup
  have hge : n ≤ xs.length := by
    have hsubset :
        ∀ x : Fin n, x ∈ List.finRange n → x ∈ xs := by
      intro x _hmem
      exact hcover x
    have hleRange :=
      list_length_le_of_nodup_subset (List.finRange n) xs
        (by
          simpa [List.finRange] using
            list_nodup_ofFn_injective (fun i : Fin n => i)
              (fun _ _ h => h))
        hsubset
    simpa [List.finRange] using hleRange
  omega

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

theorem nodePortsExcept_eq_of_val
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

end StringDiagram
end BijForm
