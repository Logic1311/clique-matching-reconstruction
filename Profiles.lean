import Lean.Elab.Tactic.Omega
import Init.Data.List.FinRange
import Init.Data.List.Perm
namespace CliqueMatching
def Feasible (b s a d : Nat) : Prop := a ≤ 2*b ∧ d ≤ 2*s
def Blocked (b s a d : Nat) : Prop :=
  (a ≤ 2*(s+1) ∧ d = 0) ∨
  (a = 0 ∧ d ≤ 2*(b+1)) ∨
  (a ≤ b ∧ d ≤ s+1)
def Ally (b s : Nat) : Nat :=
  if s = 1 then (if b+s ≤ 5 then 5 else b+s)
  else (if b+2 ≤ s+3 then b+2 else s+3)
theorem ally_lower (b s a d : Nat)
    (hb : 2 ≤ b) (hs : 1 ≤ s) (hc : 4 ≤ b+s)
    (hf : Feasible b s a d) (hu : ¬ Blocked b s a d) :
    Ally b s ≤ a+d := by
  unfold Feasible at hf
  unfold Blocked at hu
  unfold Ally
  by_cases h : s = 1
  · rw [if_pos h]
    by_cases hle : b+s ≤ 5
    · rw [if_pos hle]; omega
    · rw [if_neg hle]; omega
  · rw [if_neg h]
    by_cases hle : b+2 ≤ s+3
    · rw [if_pos hle]; omega
    · rw [if_neg hle]; omega
theorem ally_attained (b s : Nat)
    (hb : 2 ≤ b) (hs : 1 ≤ s) (hc : 4 ≤ b+s) :
    ∃ a d, Feasible b s a d ∧ ¬ Blocked b s a d ∧ a+d = Ally b s := by
  by_cases h : s = 1
  · by_cases hle : b+s ≤ 5
    · refine ⟨5, 0, ?_, ?_, ?_⟩
      · unfold Feasible; omega
      · unfold Blocked; omega
      · rw [Ally, if_pos h, if_pos hle] <;> omega
    · refine ⟨b+1, 0, ?_, ?_, ?_⟩
      · unfold Feasible; omega
      · unfold Blocked; omega
      · rw [Ally, if_pos h, if_neg hle] <;> omega
  · by_cases hle : b+2 ≤ s+3
    · refine ⟨b+1, 1, ?_, ?_, ?_⟩
      · unfold Feasible; omega
      · unfold Blocked; omega
      · rw [Ally, if_neg h, if_pos hle] <;> omega
    · refine ⟨1, s+2, ?_, ?_, ?_⟩
      · unfold Feasible; omega
      · unfold Blocked; omega
      · rw [Ally, if_neg h, if_neg hle] <;> omega
theorem blocked_upper (b s a d : Nat)
    (hf : Feasible b s a d) (h : Blocked b s a d) :
    a+d ≤ b+s+1 := by
  unfold Feasible at hf
  unfold Blocked at h
  omega
theorem blocked_attained (b s : Nat) (hb : 2 ≤ b) (hs : 1 ≤ s) :
    ∃ a d, Feasible b s a d ∧ Blocked b s a d ∧ a+d = b+s+1 := by
  refine ⟨b, s+1, ?_, ?_, ?_⟩
  · unfold Feasible; omega
  · unfold Blocked; omega
  · omega
def ValidOn {V : Type} (E : V → V → Prop) (side : V → Bool)
    (P : V → Prop) : Prop :=
  (∀ x y, P x → P y → x ≠ y → side x = side y → E x y) ∧
  (∀ x y z, P x → P y → P z → side x ≠ side y →
    side x ≠ side z → E x y → E x z → y = z)
theorem glue_validity {V : Type} (E : V → V → Prop)
    (side : V → Bool) (good : V → Prop)
    (cover : ∀ x y z : V, ∃ v, good v ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z)
    (localValid : ∀ v, good v → ValidOn E side (fun x => x ≠ v)) :
    ValidOn E side (fun _ => True) := by
  constructor
  · intro x y _ _ hxy hs
    obtain ⟨v, hg, hvx, hvy, _⟩ := cover x y x
    exact (localValid v hg).1 x y (Ne.symm hvx) (Ne.symm hvy) hxy hs
  · intro x y z _ _ _ hxy hxz exy exz
    obtain ⟨v, hg, hvx, hvy, hvz⟩ := cover x y z
    exact (localValid v hg).2 x y z (Ne.symm hvx) (Ne.symm hvy)
      (Ne.symm hvz) hxy hxz exy exz
theorem assignment_conflict {V : Type} (E : V → V → Prop)
    (p q : V → Bool) (P Q : V → Prop) (v x y : V)
    (hp : ValidOn E p P) (hq : ValidOn E q Q)
    (hpv : P v) (hpx : P x) (hpy : P y)
    (hqv : Q v) (hqx : Q x) (hqy : Q y)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (hpxv : p v = p x) (hpyv : p v = p y)
    (hqxv : q v ≠ q x) (hqyv : q v ≠ q y) : False := by
  have ex : E v x := hp.1 v x hpv hpx hvx hpxv
  have ey : E v y := hp.1 v y hpv hpy hvy hpyv
  exact hxy (hq.2 v x y hqv hqx hqy hqxv hqyv ex ey)
#print axioms ally_lower
#print axioms ally_attained
#print axioms blocked_upper
#print axioms blocked_attained
#print axioms glue_validity
#print axioms assignment_conflict

-- Explicit finite witness predicates, independent of any cardinality library.
def Three {V : Type} (P : V → Prop) : Prop :=
  ∃ a b c, P a ∧ P b ∧ P c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

def Four {V : Type} (P : V → Prop) : Prop :=
  ∃ a b c d, P a ∧ P b ∧ P c ∧ P d ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

theorem four_avoid {V : Type} {P : V → Prop}
    (h : Four P) (w : V) : Three (fun x => P x ∧ x ≠ w) := by
  rcases h with ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd⟩
  by_cases hwa : a = w
  · subst w
    exact ⟨b,c,d,⟨hb,Ne.symm hab⟩,⟨hc,Ne.symm hac⟩,⟨hd,Ne.symm had⟩,hbc,hbd,hcd⟩
  · by_cases hwb : b = w
    · subst w
      exact ⟨a,c,d,⟨ha,hab⟩,⟨hc,Ne.symm hbc⟩,⟨hd,Ne.symm hbd⟩,hac,had,hcd⟩
    · by_cases hwc : c = w
      · subst w
        exact ⟨a,b,d,⟨ha,hac⟩,⟨hb,hbc⟩,⟨hd,Ne.symm hcd⟩,hab,had,hbd⟩
      · exact ⟨a,b,c,⟨ha,hwa⟩,⟨hb,hwb⟩,⟨hc,hwc⟩,hab,hac,hbc⟩

theorem three_avoid {V : Type} {P : V → Prop}
    (h : Three P) (w : V) :
    ∃ a b, (P a ∧ a ≠ w) ∧ (P b ∧ b ≠ w) ∧ a ≠ b := by
  rcases h with ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩
  by_cases hwa : a = w
  · subst w
    exact ⟨b,c,⟨hb,Ne.symm hab⟩,⟨hc,Ne.symm hac⟩,hbc⟩
  · by_cases hwb : b = w
    · subst w
      exact ⟨a,c,⟨ha,hab⟩,⟨hc,Ne.symm hbc⟩,hac⟩
    · exact ⟨a,b,⟨ha,hwa⟩,⟨hb,hwb⟩,hab⟩

theorem four_cover {V : Type} {P : V → Prop}
    (h : Four P) (x y z : V) :
    ∃ w, P w ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  obtain ⟨a,b,ha,hb,hab⟩ := three_avoid (four_avoid h x) y
  by_cases haz : a = z
  · subst z
    exact ⟨b,hb.1.1,hb.1.2,hb.2,Ne.symm hab⟩
  · exact ⟨a,ha.1.1,ha.1.2,ha.2,haz⟩

theorem valid_congr {V : Type} (E : V → V → Prop)
    (q r : V → Bool) (P : V → Prop)
    (h : ValidOn E q P)
    (he : ∀ x y, P x → P y → (r x = r y ↔ q x = q y)) :
    ValidOn E r P := by
  constructor
  · intro x y hx hy hxy hs
    exact h.1 x y hx hy hxy ((he x y hx hy).1 hs)
  · intro x y z hx hy hz hxy hxz exy exz
    exact h.2 x y z hx hy hz
      (fun e => hxy ((he x y hx hy).2 e))
      (fun e => hxz ((he x z hx hz).2 e)) exy exz

theorem triangle_same {V : Type} (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (q : V → Bool) (P : V → Prop) (h : ValidOn E q P)
    (a b c : V) (ha : P a) (hb : P b) (hc : P c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (eab : E a b) (eac : E a c) (ebc : E b c) :
    q a = q b ∧ q a = q c := by
  have eqAB : q a = q b := by
    by_cases hs : q a = q b
    · exact hs
    · by_cases ht : q a = q c
      · have hbc' : q b ≠ q c := fun e => hs (ht.trans e.symm)
        exact False.elim (hac (h.2 b a c hb ha hc (Ne.symm hs) hbc' (symm a b eab) ebc))
      · exact False.elim (hbc (h.2 a b c ha hb hc hs ht eab eac))
  have eqAC : q a = q c := by
    by_cases ht : q a = q c
    · exact ht
    · have hcb : q c ≠ q b := fun e => ht (eqAB.trans e.symm)
      exact False.elim (hab (h.2 c a b hc ha hb (Ne.symm ht) hcb (symm a c eac) (symm b c ebc)))
  exact ⟨eqAB,eqAC⟩

def orient {V : Type} (q : V → Bool) (a x : V) : Bool :=
  decide (q x = q a)

theorem orient_eq {V : Type} (q : V → Bool) (a x y : V) :
    orient q a x = orient q a y ↔ q x = q y := by
  unfold orient
  cases hqa : q a <;> cases hqx : q x <;> cases hqy : q y <;> decide

-- Three surviving vertices of the reference large clique determine the
-- orientation of every other vertex shared by the two cards.
theorem align_on_overlap_strong {V : Type} (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (p q : V → Bool) (v w : V)
    (base : ValidOn E p (fun x => x ≠ v))
    (card : ValidOn E q (fun x => x ≠ w))
    (anchors : Three (fun x => x ≠ v ∧ x ≠ w ∧ p x = true)) :
    ∃ a : V, ValidOn E (orient q a) (fun x => x ≠ w) ∧
      ∀ x, x ≠ v → x ≠ w → orient q a x = p x := by
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := anchors
  have eab := base.1 a b ha.1 hb.1 hab (ha.2.2.trans hb.2.2.symm)
  have eac := base.1 a c ha.1 hc.1 hac (ha.2.2.trans hc.2.2.symm)
  have ebc := base.1 b c hb.1 hc.1 hbc (hb.2.2.trans hc.2.2.symm)
  have eqAB := (triangle_same E symm q (fun x => x ≠ w) card a b c
    ha.2.1 hb.2.1 hc.2.1 hab hac hbc eab eac ebc).1
  refine ⟨a, ?_, ?_⟩
  · exact valid_congr E q (orient q a) (fun x => x ≠ w) card
      (fun x y _ _ => orient_eq q a x y)
  · intro x hxv hxw
    cases hpx : p x
    · have hneq : q x ≠ q a := by
        intro hqa
        have hqb := hqa.trans eqAB
        have hpa : p x ≠ p a := by rw [hpx,ha.2.2]; decide
        have hpb : p x ≠ p b := by rw [hpx,hb.2.2]; decide
        have hxa : x ≠ a := fun e => hpa (congrArg p e)
        have hxb : x ≠ b := fun e => hpb (congrArg p e)
        have exa := card.1 x a hxw ha.2.1 hxa hqa
        have exb := card.1 x b hxw hb.2.1 hxb hqb
        exact hab (base.2 x a b hxv ha.1 hb.1 hpa hpb exa exb)
      simp [orient, hneq]
    · have heq : q x = q a := by
        by_cases hxa : x = a
        · rw [hxa]
        · by_cases hxb : x = b
          · rw [hxb]; exact eqAB.symm
          · have eax := base.1 a x ha.1 hxv (Ne.symm hxa) (ha.2.2.trans hpx.symm)
            have ebx := base.1 b x hb.1 hxv (Ne.symm hxb) (hb.2.2.trans hpx.symm)
            exact (triangle_same E symm q (fun x => x ≠ w) card a b x
              ha.2.1 hb.2.1 hxw hab (Ne.symm hxa) (Ne.symm hxb) eab eax ebx).2.symm
      simp [orient,heq]


theorem align_on_overlap {V : Type} (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (p q : V → Bool) (v w : V)
    (base : ValidOn E p (fun x => x ≠ v))
    (card : ValidOn E q (fun x => x ≠ w))
    (anchors : Three (fun x => x ≠ v ∧ x ≠ w ∧ p x = true)) :
    ∃ r : V → Bool, ValidOn E r (fun x => x ≠ w) ∧
      ∀ x, x ≠ v → x ≠ w → r x = p x := by
  obtain ⟨a,ha,hagree⟩ := align_on_overlap_strong E symm p q v w base card anchors
  exact ⟨orient q a,ha,hagree⟩


-- The central structural theorem: with four good deletions and a
-- reference clique containing four vertices, the partitions glue.
-- No restriction on the original graph is assumed beyond symmetry.
theorem structural_gluing {V : Type} (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (good : V → Prop) (v : V) (p : V → Bool)
    (hgood : Four good) (_hv : good v)
    (base : ValidOn E p (fun x => x ≠ v))
    (large : Four (fun x => x ≠ v ∧ p x = true))
    (cards : ∀ w, good w → ∃ q, ValidOn E q (fun x => x ≠ w)) :
    ∃ r : V → Bool, ValidOn E r (fun _ => True) ∧
      ∀ x, x ≠ v → r x = p x := by
  classical
  have aligned : ∀ w, good w →
      ∃ q, ValidOn E q (fun x => x ≠ w) ∧
      ∀ x, x ≠ v → x ≠ w → q x = p x := by
    intro w hw
    obtain ⟨q,hq⟩ := cards w hw
    obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := four_avoid large w
    exact align_on_overlap E symm p q v w base hq
      ⟨a,b,c,⟨ha.1.1,ha.2,ha.1.2⟩,⟨hb.1.1,hb.2,hb.1.2⟩,
        ⟨hc.1.1,hc.2,hc.1.2⟩,hab,hac,hbc⟩
  obtain ⟨w,hw,hwv,_,_⟩ := four_cover hgood v v v
  obtain ⟨q,hq,agreeq⟩ := aligned w hw
  let r : V → Bool := fun x => if x = v then q v else p x
  have hr : ∀ x, x ≠ v → r x = p x := by
    intro x hx
    simp [r,hx]
  refine ⟨r,?_,hr⟩
  apply glue_validity E r good (four_cover hgood)
  intro d hd
  by_cases hdv : d = v
  · subst d
    exact valid_congr E p r (fun x => x ≠ v) base
      (fun x y hx hy => by rw [hr x hx,hr y hy])
  · obtain ⟨t,ht,agreet⟩ := aligned d hd
    obtain ⟨a,b,ha,hb,hab⟩ := three_avoid (four_avoid large w) d
    have hqa : q a = true := (agreeq a ha.1.1.1 ha.1.2).trans ha.1.1.2
    have hqb : q b = true := (agreeq b hb.1.1.1 hb.1.2).trans hb.1.1.2
    have hta : t a = true := (agreet a ha.1.1.1 ha.2).trans ha.1.1.2
    have htb : t b = true := (agreet b hb.1.1.1 hb.2).trans hb.1.1.2
    have hqt : q v = t v := by
      cases hqv : q v <;> cases htv : t v
      · rfl
      · exact False.elim (assignment_conflict E t q (fun x => x ≠ d) (fun x => x ≠ w)
          v a b ht hq (Ne.symm hdv) ha.2 hb.2 (Ne.symm hwv) ha.1.2 hb.1.2
          (Ne.symm ha.1.1.1) (Ne.symm hb.1.1.1) hab
          (htv.trans hta.symm) (htv.trans htb.symm)
          (by rw [hqv,hqa]; decide) (by rw [hqv,hqb]; decide))
      · exact False.elim (assignment_conflict E q t (fun x => x ≠ w) (fun x => x ≠ d)
          v a b hq ht (Ne.symm hwv) ha.1.2 hb.1.2 (Ne.symm hdv) ha.2 hb.2
          (Ne.symm ha.1.1.1) (Ne.symm hb.1.1.1) hab
          (hqv.trans hqa.symm) (hqv.trans hqb.symm)
          (by rw [htv,hta]; decide) (by rw [htv,htb]; decide))
      · rfl
    have hrt : ∀ x, x ≠ d → r x = t x := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        simp [r,hqt]
      · exact (hr x hxv).trans (agreet x hxv hx).symm
    exact valid_congr E t r (fun x => x ≠ d) ht
      (fun x y hx hy => by rw [hrt x hx,hrt y hy])

#print axioms four_cover
#print axioms triangle_same
#print axioms align_on_overlap
#print axioms structural_gluing


-- Exact numerical deletion profiles of the two structural families.
-- c = b+s; k is the number of matching edges in the competitor.
def BalancedA (b s k : Nat) : Nat :=
  if k = b then 2*k else if k+1 = b then 2*(b+s-k) else 0
def BalancedB (b s k : Nat) : Nat :=
  if k = b then 2*(b+s-k) else if k = b+1 then 2*k else 0
def UnbalancedA (b s k : Nat) : Nat :=
  if k = b then k else if k+1 = b then b+s+1-k else 0
def UnbalancedB (b s k : Nat) : Nat :=
  if k = b then b+s+1-k else if k = b+1 then k else 0

def FamilyBlocks (b s a d : Nat) : Prop :=
  (∃ k, k ≤ b+s ∧ k ≠ b ∧
    a ≤ BalancedA b s k ∧ d ≤ BalancedB b s k) ∨
  (∃ k, k+1 ≤ b+s ∧
    a ≤ UnbalancedA b s k ∧ d ≤ UnbalancedB b s k)

theorem family_blocks_iff (b s a d : Nat)
    (hb : 2 ≤ b) (hs : 1 ≤ s) :
    FamilyBlocks b s a d ↔ Blocked b s a d := by
  constructor
  · intro h
    rcases h with ⟨k,hk,hne,ha,hd⟩ | ⟨k,hk,ha,hd⟩
    · unfold BalancedA at ha
      unfold BalancedB at hd
      rw [if_neg hne] at ha hd
      unfold Blocked
      by_cases h1 : k+1=b
      · rw [if_pos h1] at ha
        have h2 : k ≠ b+1 := by omega
        rw [if_neg h2] at hd
        omega
      · rw [if_neg h1] at ha
        by_cases h2 : k=b+1
        · rw [if_pos h2] at hd
          omega
        · rw [if_neg h2] at hd
          omega
    · unfold UnbalancedA at ha
      unfold UnbalancedB at hd
      unfold Blocked
      by_cases he : k=b
      · rw [if_pos he] at ha hd
        omega
      · rw [if_neg he] at ha hd
        by_cases h1 : k+1=b
        · rw [if_pos h1] at ha
          have h2 : k ≠ b+1 := by omega
          rw [if_neg h2] at hd
          omega
        · rw [if_neg h1] at ha
          by_cases h2 : k=b+1
          · rw [if_pos h2] at hd
            omega
          · rw [if_neg h2] at hd
            omega
  · intro h
    rcases h with ⟨ha,hd⟩ | ⟨ha,hd⟩ | ⟨ha,hd⟩
    · left
      have hne : b-1 ≠ b := by omega
      have h1 : b-1+1 = b := by omega
      have h2 : b-1 ≠ b+1 := by omega
      refine ⟨b-1,by omega,hne,?_,?_⟩
      · unfold BalancedA
        rw [if_neg hne,if_pos h1]
        omega
      · unfold BalancedB
        rw [if_neg hne,if_neg h2]
        omega
    · left
      have hne : b+1 ≠ b := by omega
      have h1 : b+1+1 ≠ b := by omega
      refine ⟨b+1,by omega,hne,?_,?_⟩
      · unfold BalancedA
        rw [if_neg hne,if_neg h1]
        omega
      · unfold BalancedB
        rw [if_neg hne,if_pos rfl]
        omega
    · right
      refine ⟨b,by omega,?_,?_⟩
      · unfold UnbalancedA
        rw [if_pos rfl]
        exact ha
      · unfold UnbalancedB
        rw [if_pos rfl]
        omega

theorem small_blocked (b s a d : Nat)
    (hb : 2 ≤ b) (hs : 1 ≤ s) (h : a+d ≤ 3) :
    Blocked b s a d := by
  unfold Blocked
  omega

-- If all four-or-more-card competitors are of one of the two families
-- and their multiplicities are the displayed profiles, the exact
-- reconstruction numbers follow. This is a reduction, not a theorem
-- about graph isomorphism or finite-card enumeration.
theorem profile_reduction (b s a d : Nat) (hb : 2 ≤ b) (hs : 1 ≤ s)
    (P : Prop)
    (large_only : P → a+d ≤ 3 ∨ FamilyBlocks b s a d)
    (realize : FamilyBlocks b s a d → P) :
    P ↔ Blocked b s a d := by
  constructor
  · intro h
    rcases large_only h with hsmall | hfamily
    · exact small_blocked b s a d hb hs hsmall
    · exact (family_blocks_iff b s a d hb hs).1 hfamily
  · intro h
    exact realize ((family_blocks_iff b s a d hb hs).2 h)

#print axioms family_blocks_iff
#print axioms small_blocked
#print axioms profile_reduction


-- Finite vertex cardinalities, using only Lean's standard List library.
noncomputable def Count {V : Type} (L : List V) (P : V → Prop) : Nat :=
  L.countP (fun x => @decide (P x) (Classical.propDecidable _))

noncomputable def One (P : Prop) : Nat :=
  @ite Nat P (Classical.propDecidable _) 1 0

theorem count_nil {V : Type} (P : V → Prop) : Count [] P = 0 := by
  simp [Count]

theorem count_cons {V : Type} (x : V) (L : List V) (P : V → Prop) :
    Count (x::L) P = Count L P + One (P x) := by
  classical
  unfold Count One
  rw [List.countP_cons]
  by_cases h : P x <;> simp [h]

theorem count_congr {V : Type} (L : List V) (P Q : V → Prop)
    (h : ∀ x, x ∈ L → (P x ↔ Q x)) : Count L P = Count L Q := by
  classical
  unfold Count
  apply List.countP_congr
  intro x hx
  simpa using h x hx

theorem count_zero {V : Type} (L : List V) (P : V → Prop)
    (h : ∀ x, x ∈ L → ¬ P x) : Count L P = 0 := by
  classical
  unfold Count
  apply List.countP_eq_zero.mpr
  intro x hx
  simpa using h x hx

theorem count_split {V : Type} (L : List V) (P Q : V → Prop) :
    Count L P = Count L (fun x => P x ∧ Q x) +
                Count L (fun x => P x ∧ ¬ Q x) := by
  induction L with
  | nil => simp [count_nil]
  | cons a L ih =>
    rw [count_cons, count_cons, count_cons, ih]
    by_cases hp : P a <;> by_cases hq : Q a <;> simp [One,hp,hq] <;> omega

theorem count_single {V : Type} (L : List V) (nd : L.Nodup)
    (v : V) (hv : v ∈ L) : Count L (fun x => x=v) = 1 := by
  induction L with
  | nil => simp at hv
  | cons a L ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp nd
    rw [count_cons]
    by_cases h : a=v
    · subst a
      have hz := count_zero L (fun x => x=v) (by intro x hx he; subst x; exact hna hx)
      simp [hz,One]
    · have hmem : v ∈ L := by
        rcases List.mem_cons.mp hv with he | he
        · exact False.elim (h he.symm)
        · exact he
      rw [ih hn hmem]
      simp [One,h]

theorem count_delete {V : Type} (L : List V) (nd : L.Nodup)
    (v : V) (hv : v ∈ L) (P : V → Prop) :
    Count L (fun x => P x ∧ x ≠ v) + One (P v) = Count L P := by
  rw [count_split L P (fun x => x=v)]
  have he : Count L (fun x => P x ∧ x=v) = One (P v) := by
    by_cases hp : P v
    · have eq := count_congr L (fun x => P x ∧ x=v) (fun x => x=v)
        (by intro x _; constructor; exact And.right; intro e; subst x; exact ⟨hp,rfl⟩)
      rw [eq,count_single L nd v hv]
      simp [One,hp]
    · have eq := count_zero L (fun x => P x ∧ x=v)
        (by intro x _ h; exact hp (h.2 ▸ h.1))
      simp [eq,One,hp]
  rw [he]
  exact Nat.add_comm _ _

theorem four_of_list {V : Type} (L : List V) (nd : L.Nodup)
    (hlen : 4 ≤ L.length) (P : V → Prop)
    (hp : ∀ x, x ∈ L → P x) : Four P := by
  cases L with
  | nil => simp at hlen
  | cons a L =>
    cases L with
    | nil => simp at hlen
    | cons b L =>
      cases L with
      | nil => simp at hlen
      | cons c L =>
        cases L with
        | nil => simp at hlen
        | cons d L =>
          obtain ⟨hna,hn1⟩ := List.nodup_cons.mp nd
          obtain ⟨hnb,hn2⟩ := List.nodup_cons.mp hn1
          obtain ⟨hnc,_⟩ := List.nodup_cons.mp hn2
          refine ⟨a,b,c,d,hp a (by simp),hp b (by simp),
            hp c (by simp),hp d (by simp),?_,?_,?_,?_,?_,?_⟩
          · intro h; exact hna (by simp [h])
          · intro h; exact hna (by simp [h])
          · intro h; exact hna (by simp [h])
          · intro h; exact hnb (by simp [h])
          · intro h; exact hnb (by simp [h])
          · intro h; exact hnc (by simp [h])

theorem four_of_count {V : Type} (L : List V) (nd : L.Nodup)
    (P : V → Prop) (h : 4 ≤ Count L P) : Four P := by
  classical
  let L' := L.filter (fun x => @decide (P x) (Classical.propDecidable _))
  have nd' : L'.Nodup := List.filter_sublist.nodup nd
  have hlen : 4 ≤ L'.length := by
    simpa [Count,List.countP_eq_length_filter,L'] using h
  apply four_of_list L' nd' hlen P
  intro x hx
  have hh := (List.mem_filter.mp hx).2
  simpa using hh

-- Finite-graph version of the structural classification, including the
-- two possible part sizes. The list contains each vertex exactly once.
theorem finite_structure {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L)
    (E : V → V → Prop) (symm : ∀ x y, E x y → E y x)
    (good : V → Prop) (v : V) (p : V → Bool) (c : Nat)
    (hc : 4 ≤ c) (hg : 4 ≤ Count L good) (hv : good v)
    (base : ValidOn E p (fun x => x ≠ v))
    (hx : Count L (fun x => x ≠ v ∧ p x = true) = c)
    (hy : Count L (fun x => x ≠ v ∧ p x = false) = c-1)
    (cards : ∀ w, good w → ∃ q, ValidOn E q (fun x => x ≠ w)) :
    ∃ r : V → Bool, ValidOn E r (fun _ => True) ∧
      ((Count L (fun x => r x = true) = c ∧ Count L (fun x => r x = false) = c) ∨
       (Count L (fun x => r x = true) = c+1 ∧ Count L (fun x => r x = false) = c-1)) := by
  have hlarge : Four (fun x => x ≠ v ∧ p x = true) := by
    apply four_of_count L nd
    omega
  obtain ⟨r,hr,hagree⟩ := structural_gluing E symm good v p
    (four_of_count L nd good hg) hv base hlarge cards
  refine ⟨r,hr,?_⟩
  have hxt : Count L (fun x => r x = true ∧ x ≠ v) = c := by
    rw [count_congr L (fun x => r x = true ∧ x ≠ v)
      (fun x => x ≠ v ∧ p x = true) (by
        intro x _
        constructor
        · intro h; exact ⟨h.2,(hagree x h.2).symm.trans h.1⟩
        · intro h; exact ⟨(hagree x h.1).trans h.2,h.1⟩)]
    exact hx
  have hyt : Count L (fun x => r x = false ∧ x ≠ v) = c-1 := by
    rw [count_congr L (fun x => r x = false ∧ x ≠ v)
      (fun x => x ≠ v ∧ p x = false) (by
        intro x _
        constructor
        · intro h; exact ⟨h.2,(hagree x h.2).symm.trans h.1⟩
        · intro h; exact ⟨(hagree x h.1).trans h.2,h.1⟩)]
    exact hy
  have ht := count_delete L nd v (all v) (fun x => r x = true)
  have hf := count_delete L nd v (all v) (fun x => r x = false)
  rw [hxt] at ht
  rw [hyt] at hf
  cases hv' : r v
  · simp [One,hv'] at ht hf
    left
    omega
  · simp [One,hv'] at ht hf
    right
    omega

#print axioms count_delete
#print axioms four_of_count
#print axioms finite_structure


-- Counting identities for partial matchings.
theorem count_mono {V : Type} (L : List V) (P Q : V → Prop)
    (h : ∀ x, x ∈ L → P x → Q x) : Count L P ≤ Count L Q := by
  induction L with
  | nil => simp [count_nil]
  | cons a L ih =>
    rw [count_cons,count_cons]
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hp : P a
    · have hq := h a List.mem_cons_self hp
      simp [One,hp,hq]; omega
    · by_cases hq : Q a <;> simp [One,hp,hq] <;> omega

theorem count_all {V : Type} (L : List V) : Count L (fun _ => True) = L.length := by
  induction L with
  | nil => simp [count_nil]
  | cons a L ih => simp [count_cons,ih,One]

theorem count_unique {V : Type} (L : List V) (nd : L.Nodup)
    (P : V → Prop) (hu : ∀ x y, P x → P y → x = y)
    (all : ∀ x, P x → x ∈ L) :
    Count L P = One (∃ x, P x) := by
  by_cases he : ∃ x, P x
  · obtain ⟨v,hv⟩ := he
    have h := count_congr L P (fun x => x=v) (by
      intro x _
      constructor
      · intro hx; exact hu x v hx hv
      · intro hx; subst x; exact hv)
    rw [h,count_single L nd v (all v hv)]
    simp [One,show ∃ x, P x from ⟨v,hv⟩]
  · have h := count_zero L P (fun x _ hx => he ⟨x,hx⟩)
    simp [One,he,h]

noncomputable def SumOver {V : Type} (L : List V) (f : V → Nat) : Nat :=
  (L.map f).sum
theorem sum_cons {V : Type} (a : V) (L : List V) (f : V → Nat) :
    SumOver (a::L) f = f a + SumOver L f := by rfl
theorem sum_congr {V : Type} (L : List V) (f g : V → Nat)
    (h : ∀ x, x ∈ L → f x = g x) : SumOver L f = SumOver L g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [sum_cons,sum_cons,h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
theorem sum_add {V : Type} (L : List V) (f g : V → Nat) :
    SumOver L (fun x => f x+g x) = SumOver L f + SumOver L g := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [sum_cons,sum_cons,sum_cons,ih]; omega
theorem sum_one {V : Type} (L : List V) (P : V → Prop) :
    SumOver L (fun x => One (P x)) = Count L P := by
  induction L with
  | nil => simp [SumOver,count_nil]
  | cons a L ih => rw [sum_cons,count_cons,ih]; omega

theorem sum_zero {V : Type} (L : List V) : SumOver L (fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [sum_cons,ih]

theorem double_count {V W : Type} (L : List V) (M : List W)
    (R : V → W → Prop) :
    SumOver L (fun x => Count M (R x)) =
    SumOver M (fun y => Count L (fun x => R x y)) := by
  induction L with
  | nil =>
    have hz := sum_congr M (fun y => Count [] (fun x => R x y))
      (fun _ => 0) (by intro y _; exact count_nil _)
    rw [hz]
    rw [sum_zero]
    rfl
  | cons a L ih =>
    rw [sum_cons,ih]
    have h := sum_congr M (fun y => Count (a::L) (fun x => R x y))
      (fun y => Count L (fun x => R x y) + One (R a y))
      (by intro y _; exact count_cons a L _)
    rw [h,sum_add,sum_one]
    omega

theorem count_relation_bij {V W : Type} (L : List V) (M : List W)
    (ndL : L.Nodup) (ndM : M.Nodup) (R : V → W → Prop)
    (allL : ∀ x y, R x y → x ∈ L)
    (allM : ∀ x y, R x y → y ∈ M)
    (row : ∀ x y z, R x y → R x z → y=z)
    (col : ∀ x y z, R x z → R y z → x=y) :
    Count L (fun x => ∃ y, R x y) = Count M (fun y => ∃ x, R x y) := by
  have e1 := sum_congr L (fun x => Count M (R x))
    (fun x => One (∃ y,R x y)) (by
      intro x _; exact count_unique M ndM (R x) (row x) (allM x))
  have e2 := sum_congr M (fun y => Count L (fun x => R x y))
    (fun y => One (∃ x,R x y)) (by
      intro y _; exact count_unique L ndL (fun x => R x y)
        (fun x z => col x z y) (fun x => allL x y))
  have h := double_count L M R
  rw [e1,e2,sum_one,sum_one] at h
  exact h
#print axioms count_relation_bij


def MatchedOn {V : Type} (E : V → V → Prop) (r : V → Bool)
    (P : V → Prop) (x : V) : Prop :=
  ∃ y, P y ∧ r x ≠ r y ∧ E x y

theorem matched_side_equal {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (P : V → Prop) (h : ValidOn E r P) :
    Count L (fun x => P x ∧ r x = true ∧ MatchedOn E r P x) =
    Count L (fun x => P x ∧ r x = false ∧ MatchedOn E r P x) := by
  let R : V → V → Prop := fun x y => P x ∧ P y ∧ r x = true ∧ r y = false ∧ E x y
  have hcount := count_relation_bij L L nd nd R (fun x _ _ => all x)
    (fun _ y _ => all y)
    (by
      intro x y z hy hz
      exact h.2 x y z hy.1 hy.2.1 hz.2.1
        (by rw [hy.2.2.1,hy.2.2.2.1]; decide)
        (by rw [hz.2.2.1,hz.2.2.2.1]; decide) hy.2.2.2.2 hz.2.2.2.2)
    (by
      intro x y z hx hy
      exact h.2 z x y hx.2.1 hx.1 hy.1
        (by rw [hx.2.2.2.1,hx.2.2.1]; decide)
        (by rw [hy.2.2.2.1,hy.2.2.1]; decide)
        (symm x z hx.2.2.2.2) (symm y z hy.2.2.2.2))
  have h1 := count_congr L (fun x => ∃ y, R x y)
      (fun x => P x ∧ r x = true ∧ MatchedOn E r P x) (by
    intro x _
    constructor
    · rintro ⟨y,hx,hy,rx,ry,e⟩
      exact ⟨hx,rx,y,hy,by rw [rx,ry]; decide,e⟩
    · rintro ⟨hx,rx,y,hy,hne,e⟩
      refine ⟨y,hx,hy,rx,?_,e⟩
      cases hr : r y
      · rfl
      · exact False.elim (hne (rx.trans hr.symm)))
  have h2 := count_congr L (fun y => ∃ x,R x y)
      (fun y => P y ∧ r y = false ∧ MatchedOn E r P y) (by
    intro y _
    constructor
    · rintro ⟨x,hx,hy,rx,ry,e⟩
      exact ⟨hy,ry,x,hx,by rw [rx,ry]; decide,symm x y e⟩
    · rintro ⟨hy,ry,x,hx,hne,e⟩
      refine ⟨x,hx,hy,?_,ry,symm y x e⟩
      cases hr : r x
      · exact False.elim (hne (ry.trans hr.symm))
      · rfl)
  rw [← h1,← h2]
  exact hcount

theorem valid_restrict {V : Type} (E : V → V → Prop) (r : V → Bool)
    (P Q : V → Prop) (h : ValidOn E r P) (sub : ∀ x,Q x → P x) :
    ValidOn E r Q := by
  constructor
  · intro x y hx hy hne hs
    exact h.1 x y (sub x hx) (sub y hy) hne hs
  · intro x y z hx hy hz hxy hxz exy exz
    exact h.2 x y z (sub x hx) (sub y hy) (sub z hz) hxy hxz exy exz

theorem count_side_delete {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (r : V → Bool) (v : V) (t : Bool) :
    Count L (fun x => x ≠ v ∧ r x = t) + One (r v = t) =
      Count L (fun x => r x = t) := by
  have h := count_delete L nd v (all v) (fun x => r x=t)
  rw [count_congr L (fun x => r x=t ∧ x≠v)
      (fun x => x≠v ∧ r x=t) (by intro x _; exact and_comm)] at h
  exact h

theorem matched_delete_one_side {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (h : ValidOn E r (fun _ => True)) (v : V) :
    Count L (fun x => x ≠ v ∧ r x = r v ∧ MatchedOn E r (fun y => y ≠ v) x) +
      One (MatchedOn E r (fun _ => True) v) =
    Count L (fun x => r x = r v ∧ MatchedOn E r (fun _ => True) x) := by
  have e := count_congr L
    (fun x => x ≠ v ∧ r x = r v ∧ MatchedOn E r (fun y => y ≠ v) x)
    (fun x => (r x = r v ∧ MatchedOn E r (fun _ => True) x) ∧ x ≠ v)
    (by
      intro x _
      constructor
      · rintro ⟨hx,hr,y,_,hs,e⟩
        exact ⟨⟨hr,y,True.intro,hs,e⟩,hx⟩
      · rintro ⟨⟨hr,y,_,hs,e⟩,hx⟩
        have hyv : y ≠ v := fun he => hs (hr.trans (congrArg r he).symm)
        exact ⟨hx,hr,y,hyv,hs,e⟩)
  rw [e]
  have hh := count_delete L nd v (all v)
    (fun x => r x = r v ∧ MatchedOn E r (fun _ => True) x)
  simpa using hh

theorem matched_delete {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (h : ValidOn E r (fun _ => True)) (v : V) :
    Count L (fun x => x ≠ v ∧ r x = true ∧ MatchedOn E r (fun y => y ≠ v) x) +
      One (MatchedOn E r (fun _ => True) v) =
    Count L (fun x => r x = true ∧ MatchedOn E r (fun _ => True) x) := by
  have hh := matched_delete_one_side L nd all E symm r h v
  have full := matched_side_equal L nd all E symm r (fun _ => True) h
  have loc := matched_side_equal L nd all E symm r (fun x => x≠v)
    (valid_restrict E r (fun _ => True) (fun x => x≠v) h (fun _ _ => True.intro))
  cases e : r v
  · simp only [e] at hh
    rw [loc]
    simp only [true_and] at full
    rw [full]
    exact hh
  · simpa only [e] using hh

#print axioms matched_side_equal
#print axioms matched_delete


-- A card is represented by a partition with its three invariants.
-- For clique sizes at least three these are complete graph-isomorphism
-- invariants; the abstract isomorphism lemma is proved separately.
noncomputable def SideN {V : Type} (L : List V) (P : V → Prop) (r : V → Bool) (t : Bool) : Nat :=
  Count L (fun x => P x ∧ r x = t)
noncomputable def MatchN {V : Type} (L : List V) (E : V → V → Prop)
    (P : V → Prop) (r : V → Bool) (t : Bool) : Nat :=
  Count L (fun x => P x ∧ r x = t ∧ MatchedOn E r P x)

def HasType {V : Type} (L : List V) (E : V → V → Prop)
    (P : V → Prop) (p q k : Nat) : Prop :=
  ∃ r : V → Bool, ValidOn E r P ∧
    SideN L P r true = p ∧ SideN L P r false = q ∧ MatchN L E P r true = k
def CardType {V : Type} (L : List V) (E : V → V → Prop) (c k : Nat) (v : V) : Prop :=
  HasType L E (fun x => x ≠ v) c (c-1) k

theorem match_congr {V : Type} (E : V → V → Prop) (P : V → Prop)
    (r q : V → Bool) (he : ∀ x y, P x → P y → (r x = r y ↔ q x = q y))
    (x : V) (hx : P x) : MatchedOn E r P x ↔ MatchedOn E q P x := by
  constructor
  · rintro ⟨y,hy,hn,ed⟩
    exact ⟨y,hy,fun e => hn ((he x y hx hy).2 e),ed⟩
  · rintro ⟨y,hy,hn,ed⟩
    exact ⟨y,hy,fun e => hn ((he x y hx hy).1 e),ed⟩

theorem sideN_congr {V : Type} (L : List V) (P : V → Prop)
    (r q : V → Bool) (he : ∀ x, P x → r x=q x) (t : Bool) :
    SideN L P r t = SideN L P q t := by
  unfold SideN
  apply count_congr
  intro x _
  constructor
  · rintro ⟨hx,ht⟩
    exact ⟨hx,(he x hx).symm.trans ht⟩
  · rintro ⟨hx,ht⟩
    exact ⟨hx,(he x hx).trans ht⟩

theorem matchN_congr {V : Type} (L : List V) (E : V → V → Prop) (P : V → Prop)
    (r q : V → Bool) (he : ∀ x, P x → r x=q x) (t : Bool) :
    MatchN L E P r t = MatchN L E P q t := by
  unfold MatchN
  have hpair : ∀ x y, P x → P y → (r x = r y ↔ q x = q y) := by
    intro x y hx hy
    rw [he x hx,he y hy]
  apply count_congr
  intro x _
  constructor
  · rintro ⟨hx,ht,hm⟩
    exact ⟨hx,(he x hx).symm.trans ht,(match_congr E P r q hpair x hx).1 hm⟩
  · rintro ⟨hx,ht,hm⟩
    exact ⟨hx,(he x hx).trans ht,(match_congr E P r q hpair x hx).2 hm⟩

theorem neg_eq (a b : Bool) : ((!a) = (!b)) ↔ a=b := by cases a <;> cases b <;> decide
theorem neg_eq_iff (a b : Bool) : ((!a) = b) ↔ a = !b := by cases a <;> cases b <;> decide

theorem sideN_flip {V : Type} (L : List V) (P : V → Prop) (r : V → Bool) (t : Bool) :
    SideN L P (fun x => !r x) t = SideN L P r (!t) := by
  unfold SideN
  apply count_congr
  intro x _
  exact and_congr_right (fun _ => neg_eq_iff _ _)

theorem matchN_flip {V : Type} (L : List V) (E : V → V → Prop)
    (P : V → Prop) (r : V → Bool) (t : Bool) :
    MatchN L E P (fun x => !r x) t = MatchN L E P r (!t) := by
  unfold MatchN
  apply count_congr
  intro x _
  constructor
  · rintro ⟨hx,ht,hm⟩
    exact ⟨hx,(neg_eq_iff _ _).1 ht,
      (match_congr E P (fun x => !r x) r (fun x y _ _ => neg_eq _ _) x hx).1 hm⟩
  · rintro ⟨hx,ht,hm⟩
    exact ⟨hx,(neg_eq_iff _ _).2 ht,
      (match_congr E P (fun x => !r x) r (fun x y _ _ => neg_eq _ _) x hx).2 hm⟩

theorem orient_cases {V : Type} (q : V → Bool) (a : V) :
    orient q a = q ∨ orient q a = (fun x => !q x) := by
  cases h : q a
  · right
    funext x
    unfold orient
    rw [h]
    cases q x <;> decide
  · left
    funext x
    unfold orient
    rw [h]
    cases q x <;> decide

theorem card_type_iff {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (r : V → Bool) (valid : ValidOn E r (fun _ => True))
    (large : 4 ≤ Count L (fun x => r x=true))
    (v : V) (c k : Nat) :
    CardType L E c k v ↔
    ((SideN L (fun x => x≠v) r true = c ∧ SideN L (fun x => x≠v) r false = c-1) ∨
     (SideN L (fun x => x≠v) r false = c ∧ SideN L (fun x => x≠v) r true = c-1)) ∧
     MatchN L E (fun x => x≠v) r true = k := by
  let P : V → Prop := fun x => x ≠ v
  have loc : ValidOn E r P := valid_restrict E r (fun _ => True) P valid (fun _ _ => True.intro)
  have meq : MatchN L E P r true = MatchN L E P r false :=
    matched_side_equal L nd all E symm r P loc
  constructor
  · rintro ⟨q,hq,hqt,hqf,hqm⟩
    have f := four_of_count L nd (fun x => r x=true) large
    obtain ⟨a,b,d,ha,hb,hd,hab,had,hbd⟩ := four_avoid f v
    obtain ⟨z,_,agree⟩ := align_on_overlap_strong E symm r q v v loc hq
      ⟨a,b,d,⟨ha.2,ha.2,ha.1⟩,⟨hb.2,hb.2,hb.1⟩,⟨hd.2,hd.2,hd.1⟩,hab,had,hbd⟩
    have ht := sideN_congr L P (orient q z) r (fun x hx => agree x hx hx) true
    have hf := sideN_congr L P (orient q z) r (fun x hx => agree x hx hx) false
    have hm := matchN_congr L E P (orient q z) r (fun x hx => agree x hx hx) true
    rcases orient_cases q z with he | he
    · rw [he] at ht hf hm
      change SideN L P q true = c at hqt
      change SideN L P q false = c-1 at hqf
      change MatchN L E P q true = k at hqm
      exact ⟨Or.inl ⟨ht.symm.trans hqt,hf.symm.trans hqf⟩,hm.symm.trans hqm⟩
    · rw [he,sideN_flip] at ht hf
      rw [he,matchN_flip] at hm
      have mq : MatchN L E P q true = MatchN L E P q false :=
        matched_side_equal L nd all E symm q P hq
      change SideN L P q true = c at hqt
      change SideN L P q false = c-1 at hqf
      change MatchN L E P q true = k at hqm
      exact ⟨Or.inr ⟨hf.symm.trans hqt,ht.symm.trans hqf⟩,
        hm.symm.trans (mq.symm.trans hqm)⟩
  · rintro ⟨hsize,hm⟩
    rcases hsize with ⟨ht,hf⟩ | ⟨hf,ht⟩
    · exact ⟨r,loc,ht,hf,hm⟩
    · refine ⟨fun x => !r x,?_,?_,?_,?_⟩
      · exact valid_congr E r (fun x => !r x) P loc (fun x y _ _ => neg_eq _ _)
      · rw [sideN_flip]; exact hf
      · rw [sideN_flip]; exact ht
      · rw [matchN_flip]; exact meq.symm.trans hm

#print axioms card_type_iff


noncomputable def CardN {V : Type} (L : List V) (E : V → V → Prop) (c k : Nat) : Nat :=
  Count L (CardType L E c k)

theorem split_sides {V : Type} (L : List V) (P : V → Prop) (r : V → Bool) :
    Count L P = Count L (fun x => P x ∧ r x = true) +
      Count L (fun x => P x ∧ r x = false) := by
  rw [count_split L P (fun x => r x=true)]
  have he := count_congr L (fun x => P x ∧ ¬r x=true)
      (fun x => P x ∧ r x=false) (by
        intro x _
        constructor
        · rintro ⟨hx,hq⟩
          exact ⟨hx,Bool.eq_false_iff.mpr hq⟩
        · rintro ⟨hx,hq⟩
          exact ⟨hx,Bool.eq_false_iff.mp hq⟩)
  rw [he]

theorem full_matchN_true {V : Type} (L : List V) (E : V → V → Prop)
    (r : V → Bool) (t : Bool) :
    MatchN L E (fun _ => True) r t =
      Count L (fun x => r x=t ∧ MatchedOn E r (fun _ => True) x) := by
  simp [MatchN]

theorem full_sideN_true {V : Type} (L : List V) (r : V → Bool) (t : Bool) :
    SideN L (fun _ => True) r t = Count L (fun x => r x=t) := by
  simp [SideN]

theorem count_match_total {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (valid : ValidOn E r (fun _ => True))
    (k : Nat) (hk : MatchN L E (fun _ => True) r true=k) :
    Count L (MatchedOn E r (fun _ => True)) = 2*k := by
  have eq := matched_side_equal L nd all E symm r (fun _ => True) valid
  change MatchN L E (fun _ => True) r true = MatchN L E (fun _ => True) r false at eq
  have hf := eq.symm.trans hk
  rw [full_matchN_true] at hk hf
  rw [split_sides L (MatchedOn E r (fun _ => True)) r]
  have ht' := count_congr L
    (fun x => MatchedOn E r (fun _ => True) x ∧ r x=true)
    (fun x => r x=true ∧ MatchedOn E r (fun _ => True) x)
    (by intro x _; exact and_comm)
  have hf' := count_congr L
    (fun x => MatchedOn E r (fun _ => True) x ∧ r x=false)
    (fun x => r x=false ∧ MatchedOn E r (fun _ => True) x)
    (by intro x _; exact and_comm)
  rw [ht',hf',hk,hf]
  omega

theorem count_unmatch_total {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (valid : ValidOn E r (fun _ => True))
    (p q k : Nat) (hp : SideN L (fun _ => True) r true=p)
    (hq : SideN L (fun _ => True) r false=q)
    (hk : MatchN L E (fun _ => True) r true=k) :
    Count L (fun x => ¬MatchedOn E r (fun _ => True) x) = p+q-2*k := by
  have hh := count_match_total L nd all E symm r valid k hk
  have hsplit := count_split L (fun _ => True) (MatchedOn E r (fun _ => True))
  have hs := split_sides L (fun _ => True) r
  change Count L (fun _ => True) = SideN L (fun _ => True) r true +
    SideN L (fun _ => True) r false at hs
  rw [hp,hq] at hs
  simp only [true_and] at hsplit
  rw [hh,hs] at hsplit
  omega

theorem count_unmatch_true {V : Type} (L : List V) (E : V → V → Prop)
    (r : V → Bool) (p k : Nat)
    (hp : SideN L (fun _ => True) r true=p)
    (hk : MatchN L E (fun _ => True) r true=k) :
    Count L (fun x => r x=true ∧ ¬MatchedOn E r (fun _ => True) x) = p-k := by
  rw [full_sideN_true] at hp
  rw [full_matchN_true] at hk
  have h := count_split L (fun x => r x=true) (MatchedOn E r (fun _ => True))
  rw [hp,hk] at h
  omega

theorem card_match_relation {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (valid : ValidOn E r (fun _ => True))
    (v : V) (k l : Nat) (hk : MatchN L E (fun _ => True) r true=k) :
    MatchN L E (fun x => x≠v) r true=l ↔
      (MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨
      (¬MatchedOn E r (fun _ => True) v ∧ k=l) := by
  rw [full_matchN_true] at hk
  have h := matched_delete L nd all E symm r valid v
  change MatchN L E (fun x => x≠v) r true +
      One (MatchedOn E r (fun _ => True) v) =
      Count L (fun x => r x=true ∧ MatchedOn E r (fun _ => True) x) at h
  rw [hk] at h
  by_cases hm : MatchedOn E r (fun _ => True) v <;> simp [hm,One] at h ⊢ <;> omega

theorem balanced_card_iff {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (valid : ValidOn E r (fun _ => True))
    (c k l : Nat) (hc : 4 ≤ c)
    (hp : SideN L (fun _ => True) r true=c)
    (hq : SideN L (fun _ => True) r false=c)
    (hk : MatchN L E (fun _ => True) r true=k) (v : V) :
    CardType L E c l v ↔
      (MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨
      (¬MatchedOn E r (fun _ => True) v ∧ k=l) := by
  have hp' := hp
  have hq' := hq
  rw [full_sideN_true] at hp' hq'
  rw [card_type_iff L nd all E symm r valid (by omega) v c l]
  have ht := count_side_delete L nd all r v true
  have hf := count_side_delete L nd all r v false
  change SideN L (fun x => x≠v) r true + One (r v=true) = _ at ht
  change SideN L (fun x => x≠v) r false + One (r v=false) = _ at hf
  rw [hp'] at ht
  rw [hq'] at hf
  have hs : (SideN L (fun x => x≠v) r true=c ∧ SideN L (fun x => x≠v) r false=c-1) ∨
      (SideN L (fun x => x≠v) r false=c ∧ SideN L (fun x => x≠v) r true=c-1) := by
    cases hr : r v
    · simp [One,hr] at ht hf ⊢
      left; omega
    · simp [One,hr] at ht hf ⊢
      right; omega
  rw [and_iff_right hs]
  exact card_match_relation L nd all E symm r valid v k l hk

theorem unbalanced_card_iff {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (r : V → Bool)
    (valid : ValidOn E r (fun _ => True))
    (c k l : Nat) (hc : 4 ≤ c)
    (hp : SideN L (fun _ => True) r true=c+1)
    (hq : SideN L (fun _ => True) r false=c-1)
    (hk : MatchN L E (fun _ => True) r true=k) (v : V) :
    CardType L E c l v ↔ r v=true ∧
      ((MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨
      (¬MatchedOn E r (fun _ => True) v ∧ k=l)) := by
  have hp' := hp
  have hq' := hq
  rw [full_sideN_true] at hp' hq'
  rw [card_type_iff L nd all E symm r valid (by omega) v c l]
  have ht := count_side_delete L nd all r v true
  have hf := count_side_delete L nd all r v false
  change SideN L (fun x => x≠v) r true + One (r v=true) = _ at ht
  change SideN L (fun x => x≠v) r false + One (r v=false) = _ at hf
  rw [hp'] at ht
  rw [hq'] at hf
  have hs : ((SideN L (fun x => x≠v) r true=c ∧ SideN L (fun x => x≠v) r false=c-1) ∨
      (SideN L (fun x => x≠v) r false=c ∧ SideN L (fun x => x≠v) r true=c-1)) ↔ r v=true := by
    cases hr : r v <;> simp [One,hr] at ht hf ⊢ <;> omega
  rw [hs,card_match_relation L nd all E symm r valid v k l hk]

#print axioms count_match_total
#print axioms balanced_card_iff
#print axioms unbalanced_card_iff


theorem balanced_profile {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (c k l : Nat) (hc : 4 ≤ c)
    (h : HasType L E (fun _ => True) c c k) :
    CardN L E c l = if k=l then 2*c-2*k else if k=l+1 then 2*k else 0 := by
  obtain ⟨r,valid,hp,hq,hk⟩ := h
  unfold CardN
  have he := count_congr L (CardType L E c l)
    (fun v => (MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨
      (¬MatchedOn E r (fun _ => True) v ∧ k=l))
    (fun v _ => balanced_card_iff L nd all E symm r valid c k l hc hp hq hk v)
  rw [he]
  by_cases h1 : k=l
  · have h2 : k≠l+1 := by omega
    rw [if_pos h1]
    have heq := count_congr L (fun v => (MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨ (¬MatchedOn E r (fun _ => True) v ∧ k=l)) (fun v => ¬MatchedOn E r (fun _ => True) v)
      (by intro x _; simp [h1,h2])
    rw [heq,count_unmatch_total L nd all E symm r valid c c k hp hq hk]
    omega
  · rw [if_neg h1]
    by_cases h2 : k=l+1
    · rw [if_pos h2]
      have heq := count_congr L (fun v => (MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨ (¬MatchedOn E r (fun _ => True) v ∧ k=l)) (MatchedOn E r (fun _ => True))
        (by intro x _; simp [h1,h2])
      rw [heq,count_match_total L nd all E symm r valid k hk]
    · rw [if_neg h2]
      apply count_zero
      intro x _
      simp [h1,h2]

theorem unbalanced_profile {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (c k l : Nat) (hc : 4 ≤ c)
    (h : HasType L E (fun _ => True) (c+1) (c-1) k) :
    CardN L E c l = if k=l then c+1-k else if k=l+1 then k else 0 := by
  obtain ⟨r,valid,hp,hq,hk⟩ := h
  unfold CardN
  have he := count_congr L (CardType L E c l)
    (fun v => r v=true ∧ ((MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨
      (¬MatchedOn E r (fun _ => True) v ∧ k=l)))
    (fun v _ => unbalanced_card_iff L nd all E symm r valid c k l hc hp hq hk v)
  rw [he]
  by_cases h1 : k=l
  · have h2 : k≠l+1 := by omega
    rw [if_pos h1]
    have heq := count_congr L (fun v => r v=true ∧ ((MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨ (¬MatchedOn E r (fun _ => True) v ∧ k=l)))
      (fun v => r v=true ∧ ¬MatchedOn E r (fun _ => True) v)
      (by intro x _; simp [h1,h2])
    rw [heq,count_unmatch_true L E r (c+1) k hp hk]
  · rw [if_neg h1]
    by_cases h2 : k=l+1
    · rw [if_pos h2]
      have heq := count_congr L (fun v => r v=true ∧ ((MatchedOn E r (fun _ => True) v ∧ k=l+1) ∨ (¬MatchedOn E r (fun _ => True) v ∧ k=l)))
        (fun v => r v=true ∧ MatchedOn E r (fun _ => True) v)
        (by intro x _; simp [h1,h2])
      rw [heq,← full_matchN_true L E r true,hk]
    · rw [if_neg h2]
      apply count_zero
      intro x _
      simp [h1,h2]

theorem type_capacity {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (P : V → Prop) (p q k : Nat)
    (h : HasType L E P p q k) : k ≤ p ∧ k ≤ q := by
  obtain ⟨r,valid,hp,hq,hk⟩ := h
  have ht := count_mono L (fun x => P x ∧ r x=true ∧ MatchedOn E r P x)
    (fun x => P x ∧ r x=true) (fun _ _ h => ⟨h.1,h.2.1⟩)
  have hf := count_mono L (fun x => P x ∧ r x=false ∧ MatchedOn E r P x)
    (fun x => P x ∧ r x=false) (fun _ _ h => ⟨h.1,h.2.1⟩)
  have eq := matched_side_equal L nd all E symm r P valid
  change MatchN L E P r true = MatchN L E P r false at eq
  change MatchN L E P r true ≤ SideN L P r true at ht
  change MatchN L E P r false ≤ SideN L P r false at hf
  rw [hk,hp] at ht
  rw [← eq,hk,hq] at hf
  exact ⟨ht,hf⟩

theorem card_k_unique {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x) (c k l : Nat) (hc : 4 ≤ c) (v : V)
    (h1 : CardType L E c k v) (h2 : CardType L E c l v) : k=l := by
  obtain ⟨r,vr,hr,_,hm⟩ := h1
  obtain ⟨q,vq,_,_,hqm⟩ := h2
  let P : V → Prop := fun x => x≠v
  change Count L (fun x => x≠v ∧ r x=true)=c at hr
  have f := four_of_count L nd (fun x => x≠v ∧ r x=true) (by omega)
  obtain ⟨a,b,d,ha,hb,hd,hab,had,hbd⟩ := four_avoid f v
  obtain ⟨z,_,agree⟩ := align_on_overlap_strong E symm r q v v vr vq
    ⟨a,b,d,⟨ha.1.1,ha.1.1,ha.1.2⟩,⟨hb.1.1,hb.1.1,hb.1.2⟩,
      ⟨hd.1.1,hd.1.1,hd.1.2⟩,hab,had,hbd⟩
  have eq := matchN_congr L E P (orient q z) r (fun x hx => agree x hx hx) true
  rcases orient_cases q z with he | he
  · rw [he] at eq
    exact hm.symm.trans (eq.symm.trans hqm)
  · rw [he,matchN_flip] at eq
    have eq' := matched_side_equal L nd all E symm q P vq
    change MatchN L E P q true = MatchN L E P q false at eq'
    exact hm.symm.trans (eq.symm.trans (eq'.symm.trans hqm))

theorem good_count {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (c b : Nat) (hc : 4 ≤ c) (hb : 2 ≤ b) :
    Count L (fun x => CardType L E c (b-1) x ∨ CardType L E c b x)
      = CardN L E c (b-1) + CardN L E c b := by
  let A := CardType L E c (b-1)
  let B := CardType L E c b
  have hd : ∀ x, A x → B x → False := by
    intro x ha hb'
    have he := card_k_unique L nd all E symm c (b-1) b hc x ha hb'
    omega
  have h := count_split L (fun x => A x ∨ B x) A
  have e1 := count_congr L (fun x => (A x ∨ B x) ∧ A x) A
    (by intro x _; constructor; exact And.right; intro hx; exact ⟨Or.inl hx,hx⟩)
  have e2 := count_congr L (fun x => (A x ∨ B x) ∧ ¬A x) B
    (by
      intro x _
      constructor
      · rintro ⟨ha | hb',hna⟩
        · exact False.elim (hna ha)
        · exact hb'
      · intro hx; exact ⟨Or.inr hx,fun ha => hd x ha hx⟩)
  rw [e1,e2] at h
  exact h

#print axioms balanced_profile
#print axioms unbalanced_profile
#print axioms card_k_unique
#print axioms good_count


-- Concrete witnesses, with k matched vertices on each side and separate
-- unmatched vertex sets. No assumption that a signature is realizable.
theorem nodup_map_inj {V W : Type} (L : List V) (nd : L.Nodup) (f : V → W)
    (inj : ∀ x y, f x=f y → x=y) : (L.map f).Nodup :=
  List.Pairwise.map f (fun x y h he => h (inj x y he)) nd

theorem fin_range_nd (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp [List.finRange]
  | succ n ih =>
    rw [List.finRange_succ,List.nodup_cons]
    constructor
    · intro h
      obtain ⟨x,_,hx⟩ := List.mem_map.mp h
      have he := congrArg Fin.val hx
      simp at he
    · exact nodup_map_inj _ ih Fin.succ (fun x y he => Fin.ext (by
        have e := congrArg Fin.val he
        simp at e
        exact e))

def sum_enum {V W : Type} (L : List V) (M : List W) : List (Sum V W) :=
  L.map Sum.inl ++ M.map Sum.inr

theorem sum_enum_nd {V W : Type} (L : List V) (M : List W) (nl : L.Nodup) (nm : M.Nodup) :
    (sum_enum L M).Nodup := by
  unfold sum_enum
  rw [List.nodup_append]
  refine ⟨nodup_map_inj _ nl _ (fun _ _ h => Sum.inl.inj h),
    nodup_map_inj _ nm _ (fun _ _ h => Sum.inr.inj h),?_⟩
  intro a ha b hb e
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨y,_,hy⟩ := List.mem_map.mp hb
  rw [← hy] at e
  contradiction

theorem sum_enum_all {V W : Type} (L : List V) (M : List W)
    (al : ∀ x : V, x ∈ L) (am : ∀ y : W, y ∈ M) :
    ∀ x : Sum V W, x ∈ sum_enum L M := by
  intro x
  cases x with
  | inl x => exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x,al x,rfl⟩))
  | inr y => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨y,am y,rfl⟩))

theorem count_map {V W : Type} (L : List V) (f : V → W) (P : W → Prop) :
    Count (L.map f) P = Count L (fun x => P (f x)) := by
  induction L with
  | nil => simp [count_nil]
  | cons a L ih => simp [List.map_cons,count_cons,ih]

theorem count_append {V : Type} (L M : List V) (P : V → Prop) :
    Count (L++M) P = Count L P + Count M P := by
  unfold Count
  rw [List.countP_append]

theorem count_sum_enum {V W : Type} (L : List V) (M : List W) (P : Sum V W → Prop) :
    Count (sum_enum L M) P =
      Count L (fun x => P (Sum.inl x)) + Count M (fun x => P (Sum.inr x)) := by
  unfold sum_enum
  rw [count_append,count_map,count_map]

abbrev CV (p q k : Nat) := Sum (Sum (Fin k) (Fin (p-k))) (Sum (Fin k) (Fin (q-k)))

def cvList (p q k : Nat) : List (CV p q k) :=
  sum_enum (sum_enum (List.finRange k) (List.finRange (p-k)))
    (sum_enum (List.finRange k) (List.finRange (q-k)))
def cvSide {p q k : Nat} : CV p q k → Bool
  | .inl _ => true
  | .inr _ => false
def cvCross {p q k : Nat} : CV p q k → CV p q k → Prop
  | .inl (.inl i), .inr (.inl j) => i=j
  | .inr (.inl i), .inl (.inl j) => i=j
  | _,_ => False
def cvEdge {p q k : Nat} (x y : CV p q k) : Prop :=
  (x ≠ y ∧ cvSide x=cvSide y) ∨ cvCross x y

theorem cvSymm {p q k : Nat} : ∀ x y : CV p q k, cvEdge x y → cvEdge y x := by
  intro x y h
  rcases h with ⟨hne,hs⟩ | hc
  · exact Or.inl ⟨Ne.symm hne,hs.symm⟩
  · right
    rcases x with (x | x) | (x | x) <;>
      rcases y with (y | y) | (y | y) <;> simp [cvCross] at hc ⊢
    all_goals exact hc.symm

theorem cvValid {p q k : Nat} :
    ValidOn (@cvEdge p q k) cvSide (fun _ => True) := by
  constructor
  · intro x y _ _ hne hs
    exact Or.inl ⟨hne,hs⟩
  · intro x y z _ _ _ hxy hxz exy exz
    have h1 : cvCross x y := exy.resolve_left (fun h => hxy h.2)
    have h2 : cvCross x z := exz.resolve_left (fun h => hxz h.2)
    rcases x with (x | x) | (x | x) <;>
      rcases y with (y | y) | (y | y) <;>
      rcases z with (z | z) | (z | z) <;> simp [cvCross] at h1 h2 ⊢
    all_goals exact h1.symm.trans h2

theorem cvList_nd (p q k : Nat) : (cvList p q k).Nodup :=
  sum_enum_nd _ _ (sum_enum_nd _ _ (fin_range_nd _) (fin_range_nd _))
    (sum_enum_nd _ _ (fin_range_nd _) (fin_range_nd _))
theorem cvList_all (p q k : Nat) : ∀ x : CV p q k, x ∈ cvList p q k :=
  sum_enum_all _ _ (sum_enum_all _ _ List.mem_finRange List.mem_finRange)
    (sum_enum_all _ _ List.mem_finRange List.mem_finRange)

theorem cvMatchedLeft {p q k : Nat} (i : Fin k) :
    MatchedOn (@cvEdge p q k) cvSide (fun _ => True) (.inl (.inl i)) := by
  refine ⟨.inr (.inl i),True.intro,?_,Or.inr ?_⟩
  · simp [cvSide]
  · rfl

theorem cvUnmatchedLeft {p q k : Nat} (i : Fin (p-k)) :
    ¬MatchedOn (@cvEdge p q k) cvSide (fun _ => True) (.inl (.inr i)) := by
  rintro ⟨y,_,hneq,hy⟩
  rcases hy with ⟨_,he⟩ | hc
  · exact hneq he
  · rcases y with (y | y) | (y | y) <;> exact hc

theorem count_false {V : Type} (L : List V) : Count L (fun _ => False) = 0 :=
  count_zero L _ (fun _ _ => id)

theorem cvType (p q k : Nat) (hp : k ≤ p) (hq : k ≤ q) :
    HasType (cvList p q k) (@cvEdge p q k) (fun _ => True) p q k := by
  refine ⟨cvSide,cvValid,?_,?_,?_⟩
  · unfold SideN cvList
    repeat rw [count_sum_enum]
    simp [cvSide,count_all,count_false,List.length_finRange]
    omega
  · unfold SideN cvList
    repeat rw [count_sum_enum]
    simp [cvSide,count_all,count_false,List.length_finRange]
    omega
  · unfold MatchN cvList
    repeat rw [count_sum_enum]
    have e1 := count_congr (List.finRange k)
      (fun (i : Fin k) => True ∧ @cvSide p q k (.inl (.inl i))=true ∧
        MatchedOn (@cvEdge p q k) cvSide (fun _ => True) (.inl (.inl i)))
      (fun _ => True) (by intro i _; simp [cvSide,cvMatchedLeft])
    have e2 := count_congr (List.finRange (p-k))
      (fun (i : Fin (p-k)) => True ∧ @cvSide p q k (.inl (.inr i))=true ∧
        MatchedOn (@cvEdge p q k) cvSide (fun _ => True) (.inl (.inr i)))
      (fun _ => False) (by intro i _; simp [cvSide,cvUnmatchedLeft])
    rw [e1,e2]
    simp [cvSide,count_all,count_false,List.length_finRange]

#print axioms cvType


-- Real graphs (finite enumerated vertex sets) rather than an assumed
-- list of possible competitor profiles.
def GraphBlock (b s a d : Nat) : Prop :=
  ∃ (V : Type) (L : List V) (E : V → V → Prop),
    L.Nodup ∧ (∀ x : V, x ∈ L) ∧ (∀ x y, E x y → E y x) ∧
    (∀ x, ¬E x x) ∧ L.length=2*(b+s) ∧
    ¬HasType L E (fun _ => True) (b+s) (b+s) b ∧
    a ≤ CardN L E (b+s) (b-1) ∧ d ≤ CardN L E (b+s) b

theorem large_competitor {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x ∈ L) (E : V → V → Prop)
    (symm : ∀ x y, E x y → E y x)
    (b s a d : Nat) (hb : 2 ≤ b) (hs : 1 ≤ s) (hc : 4 ≤ b+s)
    (notTarget : ¬HasType L E (fun _ => True) (b+s) (b+s) b)
    (ha : a ≤ CardN L E (b+s) (b-1)) (hd : d ≤ CardN L E (b+s) b)
    (large : 4 ≤ a+d) : FamilyBlocks b s a d := by
  let c := b+s
  change a ≤ CardN L E c (b-1) at ha
  change d ≤ CardN L E c b at hd
  change ¬HasType L E (fun _ => True) c c b at notTarget
  let good : V → Prop := fun v => CardType L E c (b-1) v ∨ CardType L E c b v
  have hcount := good_count L nd all E symm c b hc hb
  change Count L good = CardN L E c (b-1)+CardN L E c b at hcount
  have hlarge : 4 ≤ Count L good := by omega
  have hg := four_of_count L nd good hlarge
  obtain ⟨v,_,_,_,hv,_,_,_,_,_,_,_,_,_⟩ := hg
  have ht : ∃ p : V → Bool, ValidOn E p (fun x => x≠v) ∧
      Count L (fun x => x≠v ∧ p x=true)=c ∧
      Count L (fun x => x≠v ∧ p x=false)=c-1 := by
    rcases hv with hv | hv
    · obtain ⟨p,hp,ht,hf,_⟩ := hv
      exact ⟨p,hp,ht,hf⟩
    · obtain ⟨p,hp,ht,hf,_⟩ := hv
      exact ⟨p,hp,ht,hf⟩
  obtain ⟨p,hp,ht,hf⟩ := ht
  have cards : ∀ w, good w → ∃ q, ValidOn E q (fun x => x≠w) := by
    intro w hw
    rcases hw with hw | hw
    · obtain ⟨q,hq,_⟩ := hw; exact ⟨q,hq⟩
    · obtain ⟨q,hq,_⟩ := hw; exact ⟨q,hq⟩
  obtain ⟨r,vr,hsize⟩ := finite_structure L nd all E symm good v p c hc hlarge hv hp ht hf cards
  let k := MatchN L E (fun _ => True) r true
  rcases hsize with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · have ty : HasType L E (fun _ => True) c c k := ⟨r,vr,by simpa [SideN] using hp,by simpa [SideN] using hq,rfl⟩
    have hk := (type_capacity L nd all E symm (fun _ => True) c c k ty).1
    have hne : k≠b := by
      intro he
      apply notTarget
      rw [← he]
      exact ty
    have ea := balanced_profile L nd all E symm c k (b-1) hc ty
    have eb := balanced_profile L nd all E symm c k b hc ty
    left
    refine ⟨k,hk,hne,?_,?_⟩
    · unfold BalancedA
      change a ≤ _ at ha
      dsimp [c] at ea ha
      rw [if_neg hne]
      by_cases h1 : k+1=b
      · rw [if_pos h1]
        have h0 : k=b-1 := by omega
        rw [if_pos h0] at ea
        omega
      · rw [if_neg h1]
        have h0 : k≠b-1 := by omega
        have h0' : k≠b-1+1 := by omega
        rw [if_neg h0,if_neg h0'] at ea
        omega
    · unfold BalancedB
      rw [if_neg hne]
      rw [if_neg hne] at eb
      rw [eb] at hd
      exact hd
  · have ty : HasType L E (fun _ => True) (c+1) (c-1) k := ⟨r,vr,by simpa [SideN] using hp,by simpa [SideN] using hq,rfl⟩
    have hk := (type_capacity L nd all E symm (fun _ => True) (c+1) (c-1) k ty).2
    have ea := unbalanced_profile L nd all E symm c k (b-1) hc ty
    have eb := unbalanced_profile L nd all E symm c k b hc ty
    right
    refine ⟨k,by omega,?_,?_⟩
    · unfold UnbalancedA
      dsimp [c] at ea ha
      by_cases h1 : k=b
      · rw [if_pos h1]
        have h0 : k≠b-1 := by omega
        have h0' : k=b-1+1 := by omega
        rw [if_neg h0,if_pos h0'] at ea
        omega
      · rw [if_neg h1]
        by_cases h2 : k+1=b
        · rw [if_pos h2]
          have h0 : k=b-1 := by omega
          rw [if_pos h0] at ea
          omega
        · rw [if_neg h2]
          have h0 : k≠b-1 := by omega
          have h0' : k≠b-1+1 := by omega
          rw [if_neg h0,if_neg h0'] at ea
          omega
    · unfold UnbalancedB
      rw [eb] at hd
      exact hd

theorem cvIrrefl {p q k : Nat} : ∀ x : CV p q k, ¬cvEdge x x := by
  intro x h
  rcases h with ⟨hne,_⟩ | hc
  · exact hne rfl
  · rcases x with (x | x) | (x | x) <;> exact hc

theorem cvLength (p q k : Nat) (hp : k≤p) (hq : k≤q) :
    (cvList p q k).length=p+q := by
  simp [cvList,sum_enum,List.length_finRange]
  omega

theorem canonical_balanced_block (b s a d k : Nat) (hb : 2≤b)
    (hs : 1≤s) (hc : 4≤b+s) (hk : k≤b+s) (hne : k≠b)
    (ha : a≤BalancedA b s k) (hd : d≤BalancedB b s k) :
    GraphBlock b s a d := by
  let c := b+s
  let L := cvList c c k
  let E := @cvEdge c c k
  have nd : L.Nodup := cvList_nd c c k
  have all : ∀ x, x ∈ L := cvList_all c c k
  have symm : ∀ x y, E x y → E y x := cvSymm
  have ty : HasType L E (fun _ => True) c c k := cvType c c k hk hk
  have ea := balanced_profile L nd all E symm c k (b-1) hc ty
  have eb := balanced_profile L nd all E symm c k b hc ty
  refine ⟨CV c c k,L,E,nd,all,symm,cvIrrefl,?_,?_,?_,?_⟩
  · have hlen := cvLength c c k hk hk
    change L.length=c+c at hlen
    omega
  · intro ht
    have ea' := balanced_profile L nd all E symm c b (b-1) hc ht
    have eb' := balanced_profile L nd all E symm c b b hc ht
    have h0 : b≠b-1 := by omega
    have h1 : b=b-1+1 := by omega
    rw [if_neg h0,if_pos h1] at ea'
    rw [if_pos rfl] at eb'
    rw [if_neg hne] at eb
    by_cases h2 : k=b+1
    · rw [if_pos h2] at eb
      have h0' : k≠b-1 := by omega
      have h1' : k≠b-1+1 := by omega
      rw [if_neg h0',if_neg h1'] at ea
      omega
    · rw [if_neg h2] at eb
      omega
  · change a ≤ CardN L E c (b-1)
    unfold BalancedA at ha
    dsimp [c] at ea ⊢
    rw [if_neg hne] at ha
    by_cases h1 : k+1=b
    · rw [if_pos h1] at ha
      have h0 : k=b-1 := by omega
      rw [if_pos h0] at ea
      omega
    · rw [if_neg h1] at ha
      omega
  · change d ≤ CardN L E c b
    unfold BalancedB at hd
    rw [if_neg hne] at hd
    rw [if_neg hne] at eb
    omega

theorem canonical_unbalanced_block (b s a d k : Nat) (hb : 2≤b)
    (hs : 1≤s) (hc : 4≤b+s) (hk : k+1≤b+s)
    (ha : a≤UnbalancedA b s k) (hd : d≤UnbalancedB b s k) :
    GraphBlock b s a d := by
  let c := b+s
  let L := cvList (c+1) (c-1) k
  let E := @cvEdge (c+1) (c-1) k
  have nd : L.Nodup := cvList_nd (c+1) (c-1) k
  have all : ∀ x, x ∈ L := cvList_all (c+1) (c-1) k
  have symm : ∀ x y, E x y → E y x := cvSymm
  have h1 : k≤c+1 := by omega
  have h2 : k≤c-1 := by omega
  have ty : HasType L E (fun _ => True) (c+1) (c-1) k := cvType (c+1) (c-1) k h1 h2
  have ea := unbalanced_profile L nd all E symm c k (b-1) hc ty
  have eb := unbalanced_profile L nd all E symm c k b hc ty
  refine ⟨CV (c+1) (c-1) k,L,E,nd,all,symm,cvIrrefl,?_,?_,?_,?_⟩
  · have hlen := cvLength (c+1) (c-1) k h1 h2
    change L.length=c+1+(c-1) at hlen
    omega
  · intro ht
    have ea' := balanced_profile L nd all E symm c b (b-1) hc ht
    have eb' := balanced_profile L nd all E symm c b b hc ht
    have h0 : b≠b-1 := by omega
    have h1' : b=b-1+1 := by omega
    rw [if_neg h0,if_pos h1'] at ea'
    rw [if_pos rfl] at eb'
    by_cases e : k=b
    · have h0' : k≠b-1 := by omega
      have h1'' : k=b-1+1 := by omega
      rw [if_neg h0',if_pos h1''] at ea
      omega
    · rw [if_neg e] at eb
      by_cases e2 : k=b+1
      · have h0' : k≠b-1 := by omega
        have h1'' : k≠b-1+1 := by omega
        rw [if_neg h0',if_neg h1''] at ea
        omega
      · rw [if_neg e2] at eb
        omega
  · change a ≤ CardN L E c (b-1)
    unfold UnbalancedA at ha
    dsimp [c] at ea ⊢
    by_cases h : k=b
    · rw [if_pos h] at ha
      have h0 : k≠b-1 := by omega
      have h0' : k=b-1+1 := by omega
      rw [if_neg h0,if_pos h0'] at ea
      omega
    · rw [if_neg h] at ha
      by_cases h' : k+1=b
      · rw [if_pos h'] at ha
        have h0 : k=b-1 := by omega
        rw [if_pos h0] at ea
        omega
      · rw [if_neg h'] at ha
        omega
  · change d ≤ CardN L E c b
    unfold UnbalancedB at hd
    rw [eb]
    exact hd

theorem graph_block_iff (b s a d : Nat) (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    GraphBlock b s a d ↔ Blocked b s a d := by
  constructor
  · rintro ⟨V,L,E,nd,all,symm,_,_,ht,ha,hd⟩
    by_cases hsmall : a+d≤3
    · exact small_blocked b s a d hb hs hsmall
    · exact (family_blocks_iff b s a d hb hs).1
        (large_competitor L nd all E symm b s a d hb hs hc ht ha hd (by omega))
  · intro h
    rcases (family_blocks_iff b s a d hb hs).2 h with
      ⟨k,hk,hne,ha,hd⟩ | ⟨k,hk,ha,hd⟩
    · exact canonical_balanced_block b s a d k hb hs hc hk hne ha hd
    · exact canonical_unbalanced_block b s a d k hb hs hc hk ha hd

-- The two extremal characterizations refer to all finite simple graphs.
-- The isomorphism interpretation of HasType is handled by the structural
-- representation theorem, not assumed as a cardinality hypothesis.
theorem graph_ally (b s : Nat) (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    (∀ a d, Feasible b s a d → ¬GraphBlock b s a d → Ally b s≤a+d) ∧
    (∃ a d, Feasible b s a d ∧ ¬GraphBlock b s a d ∧ a+d=Ally b s) := by
  constructor
  · intro a d hf hu
    exact ally_lower b s a d hb hs hc hf (fun h => hu ((graph_block_iff b s a d hb hs hc).2 h))
  · obtain ⟨a,d,hf,hu,he⟩ := ally_attained b s hb hs hc
    exact ⟨a,d,hf,fun h => hu ((graph_block_iff b s a d hb hs hc).1 h),he⟩

theorem graph_adversary (b s : Nat) (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    (∀ a d, Feasible b s a d → GraphBlock b s a d → a+d≤b+s+1) ∧
    (∃ a d, Feasible b s a d ∧ GraphBlock b s a d ∧ a+d=b+s+1) := by
  constructor
  · intro a d hf hu
    exact blocked_upper b s a d hf ((graph_block_iff b s a d hb hs hc).1 hu)
  · obtain ⟨a,d,hf,hu,he⟩ := blocked_attained b s hb hs
    exact ⟨a,d,hf,(graph_block_iff b s a d hb hs hc).2 hu,he⟩

#print axioms graph_block_iff
#print axioms graph_ally
#print axioms graph_adversary


-- A bijection between two predicates, represented by its graph.
structure Pairing {V W : Type} (P : V → Prop) (Q : W → Prop)
    (R : V → W → Prop) : Prop where
  support : ∀ x y, R x y → P x ∧ Q y
  left : ∀ x, P x → ∃ y, R x y
  right : ∀ y, Q y → ∃ x, R x y
  row : ∀ x y z, R x y → R x z → y=z
  col : ∀ x y z, R x z → R y z → x=y

theorem pairing_count {V W : Type} (L : List V) (M : List W)
    (ndL : L.Nodup) (ndM : M.Nodup)
    (allL : ∀ x : V, x ∈ L) (allM : ∀ y : W, y ∈ M)
    (P : V → Prop) (Q : W → Prop) (R : V → W → Prop)
    (h : Pairing P Q R) : Count L P = Count M Q := by
  have he := count_relation_bij L M ndL ndM R (fun x _ _ => allL x)
    (fun _ y _ => allM y) h.row h.col
  rw [count_congr L (fun x => ∃ y,R x y) P
      (by intro x _; constructor; rintro ⟨y,hy⟩; exact (h.support x y hy).1; exact h.left x),
      count_congr M (fun y => ∃ x,R x y) Q
      (by intro y _; constructor; rintro ⟨x,hx⟩; exact (h.support x y hx).2; exact h.right y)] at he
  exact he

theorem pair_lists {V W : Type} (L : List V) (M : List W)
    (ndL : L.Nodup) (ndM : M.Nodup) (hlen : L.length=M.length) :
    ∃ R : V → W → Prop, Pairing (fun x => x ∈ L) (fun y => y ∈ M) R := by
  induction L generalizing M with
  | nil =>
    cases M with
    | nil =>
      refine ⟨fun _ _ => False,⟨?_,?_,?_,?_,?_⟩⟩
      · intro x y h; contradiction
      · intro x h; simp at h
      · intro y h; simp at h
      · intro x y z h; contradiction
      · intro x y z h; contradiction
    | cons b M => simp at hlen
  | cons a L ih =>
    cases M with
    | nil => simp at hlen
    | cons b M =>
      obtain ⟨hna,nda⟩ := List.nodup_cons.mp ndL
      obtain ⟨hnb,ndb⟩ := List.nodup_cons.mp ndM
      have hl : L.length=M.length := by simpa using hlen
      obtain ⟨R,hR⟩ := ih M nda ndb hl
      refine ⟨fun x y => (x=a ∧ y=b) ∨ R x y,⟨?_,?_,?_,?_,?_⟩⟩
      · intro x y h
        rcases h with ⟨rfl,rfl⟩ | hr
        · exact ⟨List.mem_cons_self,List.mem_cons_self⟩
        · exact ⟨List.mem_cons_of_mem _ (hR.support x y hr).1,
            List.mem_cons_of_mem _ (hR.support x y hr).2⟩
      · intro x hx
        rcases List.mem_cons.mp hx with he | he
        · exact ⟨b,Or.inl ⟨he,rfl⟩⟩
        · obtain ⟨y,hy⟩ := hR.left x he
          exact ⟨y,Or.inr hy⟩
      · intro y hy
        rcases List.mem_cons.mp hy with he | he
        · exact ⟨a,Or.inl ⟨rfl,he⟩⟩
        · obtain ⟨x,hx⟩ := hR.right y he
          exact ⟨x,Or.inr hx⟩
      · intro x y z hy hz
        rcases hy with ⟨hx,hy⟩ | hy <;> rcases hz with ⟨hx',hz⟩ | hz
        · exact hy.trans hz.symm
        · subst x; exact False.elim (hna (hR.support a z hz).1)
        · subst x; exact False.elim (hna (hR.support a y hy).1)
        · exact hR.row x y z hy hz
      · intro x y z hx hy
        rcases hx with ⟨hx,hz⟩ | hx <;> rcases hy with ⟨hy,hz'⟩ | hy
        · exact hx.trans hy.symm
        · subst z; exact False.elim (hnb (hR.support y b hy).2)
        · subst z; exact False.elim (hnb (hR.support x b hx).2)
        · exact hR.col x y z hx hy

theorem pairing_exists {V W : Type} (L : List V) (M : List W)
    (ndL : L.Nodup) (ndM : M.Nodup)
    (allL : ∀ x : V, x ∈ L) (allM : ∀ y : W, y ∈ M)
    (P : V → Prop) (Q : W → Prop)
    (he : Count L P=Count M Q) :
    ∃ R : V → W → Prop, Pairing P Q R := by
  classical
  let L' := L.filter (fun x => @decide (P x) (Classical.propDecidable _))
  let M' := M.filter (fun y => @decide (Q y) (Classical.propDecidable _))
  have hlen : L'.length=M'.length := by
    simpa [Count,List.countP_eq_length_filter,L',M'] using he
  obtain ⟨R,hR⟩ := pair_lists L' M' (List.filter_sublist.nodup ndL)
    (List.filter_sublist.nodup ndM) hlen
  have pl : ∀ x, x ∈ L' ↔ P x := by intro x; simp [L',allL x]
  have pm : ∀ y, y ∈ M' ↔ Q y := by intro y; simp [M',allM y]
  exact ⟨R,⟨(fun x y h => ⟨(pl x).1 (hR.support x y h).1,(pm y).1 (hR.support x y h).2⟩),
    (fun x h => hR.left x ((pl x).2 h)), (fun y h => hR.right y ((pm y).2 h)),
    hR.row,hR.col⟩⟩

theorem pairing_symm {V W : Type} (P : V → Prop) (Q : W → Prop) (R : V → W → Prop)
    (h : Pairing P Q R) : Pairing Q P (fun y x => R x y) :=
  ⟨(fun x y e => ⟨(h.support y x e).2,(h.support y x e).1⟩),
    h.right,h.left,(fun x y z => h.col y z x),(fun x y z => h.row z x y)⟩

theorem pairing_comp {V W Z : Type} (P : V → Prop) (Q : W → Prop) (S : Z → Prop)
    (R : V → W → Prop) (T : W → Z → Prop)
    (hr : Pairing P Q R) (ht : Pairing Q S T) :
    Pairing P S (fun x z => ∃ y,R x y ∧ T y z) := by
  constructor
  · rintro x z ⟨y,hy,hz⟩
    exact ⟨(hr.support x y hy).1,(ht.support y z hz).2⟩
  · intro x hx
    obtain ⟨y,hy⟩ := hr.left x hx
    obtain ⟨z,hz⟩ := ht.left y (hr.support x y hy).2
    exact ⟨z,y,hy,hz⟩
  · intro z hz
    obtain ⟨y,hy⟩ := ht.right z hz
    obtain ⟨x,hx⟩ := hr.right y (ht.support y z hy).1
    exact ⟨x,y,hx,hy⟩
  · rintro x z w ⟨y,hy,hz⟩ ⟨y',hy',hw⟩
    have e := hr.row x y y' hy hy'
    subst y'
    exact ht.row y z w hz hw
  · rintro x u z ⟨y,hy,hz⟩ ⟨y',hy',hz'⟩
    have e := ht.col y y' z hz hz'
    subst y'
    exact hr.col x u y hy hy'

theorem pairing_union {V W : Type} (P P' : V → Prop) (Q Q' : W → Prop)
    (R R' : V → W → Prop) (hr : Pairing P Q R) (hr' : Pairing P' Q' R')
    (dp : ∀ x, P x → P' x → False) (dq : ∀ y, Q y → Q' y → False) :
    Pairing (fun x => P x ∨ P' x) (fun y => Q y ∨ Q' y) (fun x y => R x y ∨ R' x y) := by
  constructor
  · intro x y h
    rcases h with h|h
    · exact ⟨Or.inl (hr.support x y h).1,Or.inl (hr.support x y h).2⟩
    · exact ⟨Or.inr (hr'.support x y h).1,Or.inr (hr'.support x y h).2⟩
  · intro x h
    rcases h with h|h
    · obtain ⟨y,hy⟩ := hr.left x h; exact ⟨y,Or.inl hy⟩
    · obtain ⟨y,hy⟩ := hr'.left x h; exact ⟨y,Or.inr hy⟩
  · intro y h
    rcases h with h|h
    · obtain ⟨x,hx⟩ := hr.right y h; exact ⟨x,Or.inl hx⟩
    · obtain ⟨x,hx⟩ := hr'.right y h; exact ⟨x,Or.inr hx⟩
  · intro x y z h h'
    rcases h with h|h <;> rcases h' with h'|h'
    · exact hr.row x y z h h'
    · exact False.elim (dp x (hr.support x y h).1 (hr'.support x z h').1)
    · exact False.elim (dp x (hr.support x z h').1 (hr'.support x y h).1)
    · exact hr'.row x y z h h'
  · intro x z y h h'
    rcases h with h|h <;> rcases h' with h'|h'
    · exact hr.col x z y h h'
    · exact False.elim (dq y (hr.support x y h).2 (hr'.support z y h').2)
    · exact False.elim (dq y (hr.support z y h').2 (hr'.support x y h).2)
    · exact hr'.col x z y h h'

theorem pairing_congr {V W : Type} (P P' : V → Prop) (Q Q' : W → Prop)
    (R : V → W → Prop) (h : Pairing P Q R)
    (ep : ∀ x, P x ↔ P' x) (eq : ∀ y, Q y ↔ Q' y) :
    Pairing P' Q' R :=
  ⟨(fun x y h' => ⟨(ep x).1 (h.support x y h').1,(eq y).1 (h.support x y h').2⟩),
    (fun x hx => h.left x ((ep x).2 hx)), (fun y hy => h.right y ((eq y).2 hy)),
    h.row,h.col⟩

def IsoOn {V W : Type} (E : V → V → Prop) (F : W → W → Prop)
    (P : V → Prop) (Q : W → Prop) : Prop :=
  ∃ R : V → W → Prop, Pairing P Q R ∧
    ∀ x x' y y', R x y → R x' y' → (E x x' ↔ F y y')

theorem iso_symm {V W : Type} (E : V → V → Prop) (F : W → W → Prop)
    (P : V → Prop) (Q : W → Prop) (h : IsoOn E F P Q) :
    IsoOn F E Q P := by
  obtain ⟨R,hR,he⟩ := h
  exact ⟨fun y x => R x y,pairing_symm P Q R hR,
    fun x x' y y' h1 h2 => (he y y' x x' h1 h2).symm⟩

#print axioms pairing_exists


def OnMatch {V : Type} (E : V → V → Prop) (r : V → Bool)
    (P : V → Prop) (t : Bool) (x : V) : Prop :=
  P x ∧ r x=t ∧ MatchedOn E r P x
def OnUnmatch {V : Type} (E : V → V → Prop) (r : V → Bool)
    (P : V → Prop) (t : Bool) (x : V) : Prop :=
  P x ∧ r x=t ∧ ¬MatchedOn E r P x
def CrossLR {V : Type} (E : V → V → Prop) (r : V → Bool)
    (P : V → Prop) (x y : V) : Prop :=
  P x ∧ P y ∧ r x=true ∧ r y=false ∧ E x y

theorem cross_pairing {V : Type} (E : V → V → Prop)
    (symm : ∀ x y,E x y → E y x)
    (r : V → Bool) (P : V → Prop) (h : ValidOn E r P) :
    Pairing (OnMatch E r P true) (OnMatch E r P false) (CrossLR E r P) := by
  constructor
  · rintro x y ⟨hx,hy,rx,ry,e⟩
    have hn : r x ≠ r y := by rw [rx,ry]; decide
    exact ⟨⟨hx,rx,y,hy,hn,e⟩,⟨hy,ry,x,hx,Ne.symm hn,symm x y e⟩⟩
  · rintro x ⟨hx,rx,y,hy,hn,e⟩
    refine ⟨y,hx,hy,rx,?_,e⟩
    cases he : r y
    · rfl
    · exact False.elim (hn (rx.trans he.symm))
  · rintro y ⟨hy,ry,x,hx,hn,e⟩
    refine ⟨x,hx,hy,?_,ry,symm y x e⟩
    cases he : r x
    · exact False.elim (hn (ry.trans he.symm))
    · rfl
  · rintro x y z ⟨hx,hy,rx,ry,e⟩ ⟨_,hz,_,rz,e'⟩
    exact h.2 x y z hx hy hz
      (by rw [rx,ry]; decide) (by rw [rx,rz]; decide) e e'
  · rintro x y z ⟨hx,hz,rx,rz,e⟩ ⟨hy,_,ry,_,e'⟩
    exact h.2 z x y hz hx hy
      (by rw [rz,rx]; decide) (by rw [rz,ry]; decide)
      (symm x z e) (symm y z e')

theorem on_unmatch_count {V : Type} (L : List V) (E : V → V → Prop)
    (P : V → Prop) (r : V → Bool) (t : Bool) :
    Count L (OnUnmatch E r P t) = SideN L P r t - MatchN L E P r t := by
  have h := count_split L (fun x => P x ∧ r x=t) (MatchedOn E r P)
  change SideN L P r t = _ at h
  have hm := count_congr L (fun x => (P x ∧ r x=t) ∧ MatchedOn E r P x)
    (OnMatch E r P t) (by intro x _; simp [OnMatch,and_assoc])
  have hu := count_congr L (fun x => (P x ∧ r x=t) ∧ ¬MatchedOn E r P x)
    (OnUnmatch E r P t) (by intro x _; simp [OnUnmatch,and_assoc])
  rw [hm,hu] at h
  change SideN L P r t = MatchN L E P r t + Count L (OnUnmatch E r P t) at h
  omega

theorem side_partition {V : Type} (E : V → V → Prop) (r : V → Bool)
    (P : V → Prop) (t : Bool) (x : V) :
    (OnMatch E r P t x ∨ OnUnmatch E r P t x) ↔ P x ∧ r x=t := by
  classical
  unfold OnMatch OnUnmatch
  constructor
  · rintro (h | h) <;> exact ⟨h.1,h.2.1⟩
  · intro h
    by_cases hm : MatchedOn E r P x
    · exact Or.inl ⟨h.1,h.2,hm⟩
    · exact Or.inr ⟨h.1,h.2,hm⟩

theorem cross_edge_transport {V W : Type}
    (E : V → V → Prop) (F : W → W → Prop) (r : V → Bool) (t : W → Bool)
    (P : V → Prop) (Q : W → Prop)
    (C : V → V → Prop) (D : W → W → Prop)
    (R : V → W → Prop) (U : V → W → Prop) (Z : V → W → Prop)
    (hC : C = CrossLR E r P) (hD : D = CrossLR F t Q)
    (pc : Pairing (OnMatch E r P true) (OnMatch E r P false) C)
    (pd : Pairing (OnMatch F t Q true) (OnMatch F t Q false) D)
    (pr : Pairing (OnMatch E r P true) (OnMatch F t Q true) R)
    (pu : Pairing (OnUnmatch E r P true) (OnUnmatch F t Q true) U)
    (pz : Pairing (OnUnmatch E r P false) (OnUnmatch F t Q false) Z)
    (x x' : V) (y y' : W)
    (hl : R x y ∨ U x y)
    (hr : (∃ b, (∃ a,C a x' ∧ R a b) ∧ D b y') ∨ Z x' y') :
    E x x' ↔ F y y' := by
  subst C
  subst D
  rcases hl with hl | hl
  · have hx := (pr.support x y hl).1
    have hy := (pr.support x y hl).2
    rcases hr with ⟨b,⟨a,hc,hab⟩,hd⟩ | hr
    · constructor
      · intro e
        have hc' : CrossLR E r P x x' := ⟨hx.1,hc.2.1,hx.2.1,hc.2.2.2.1,e⟩
        have ha := pc.col x a x' hc' hc
        subst a
        have he := pr.row x y b hl hab
        subst b
        exact hd.2.2.2.2
      · intro e
        have hd' : CrossLR F t Q y y' := ⟨hy.1,hd.2.1,hy.2.1,hd.2.2.2.1,e⟩
        have he := pd.col y b y' hd' hd
        subst b
        have ha := pr.col x a y hl hab
        subst a
        exact hc.2.2.2.2
    · have hx' := (pz.support x' y' hr).1
      have hy' := (pz.support x' y' hr).2
      constructor
      · intro e
        exact False.elim (hx.2.2.elim (fun w hw => False.elim (by
          have hcross : CrossLR E r P x x' := ⟨hx.1,hx'.1,hx.2.1,hx'.2.1,e⟩
          exact hx'.2.2 (pc.support x x' hcross).2.2.2)))
      · intro e
        have hcross : CrossLR F t Q y y' := ⟨hy.1,hy'.1,hy.2.1,hy'.2.1,e⟩
        exact False.elim (hy'.2.2 (pd.support y y' hcross).2.2.2)
  · have hx := (pu.support x y hl).1
    have hy := (pu.support x y hl).2
    have sides : (P x' ∧ r x'=false) ∧ (Q y' ∧ t y'=false) := by
      rcases hr with ⟨b,⟨a,hc,_⟩,hd⟩ | hz
      · exact ⟨⟨hc.2.1,hc.2.2.2.1⟩,⟨hd.2.1,hd.2.2.2.1⟩⟩
      · have h := pz.support x' y' hz
        exact ⟨⟨h.1.1,h.1.2.1⟩,⟨h.2.1,h.2.2.1⟩⟩
    constructor
    · intro e
      exact False.elim (hx.2.2 ⟨x',sides.1.1,by rw [hx.2.1,sides.1.2]; decide,e⟩)
    · intro e
      exact False.elim (hy.2.2 ⟨y',sides.2.1,by rw [hy.2.1,sides.2.2]; decide,e⟩)



theorem same_side_transport {V W : Type}
    (E : V → V → Prop) (F : W → W → Prop) (r : V → Bool) (t : W → Bool)
    (P : V → Prop) (Q : W → Prop)
    (irE : ∀ x, ¬E x x) (irF : ∀ y, ¬F y y)
    (vr : ValidOn E r P) (vt : ValidOn F t Q)
    (R : V → W → Prop) (hR : Pairing P Q R)
    (x x' : V) (y y' : W) (h : R x y) (h' : R x' y')
    (er : r x=r x') (et : t y=t y') :
    E x x' ↔ F y y' := by
  constructor
  · intro e
    have hn : x≠x' := fun he => irE x (he.symm ▸ e)
    have hm : y≠y' := by
      intro he; subst y'; exact hn (hR.col x x' y h h')
    exact vt.1 y y' (hR.support x y h).2 (hR.support x' y' h').2 hm et
  · intro e
    have hn : y≠y' := fun he => irF y (he.symm ▸ e)
    have hm : x≠x' := by
      intro he; subst x'; exact hn (hR.row x y y' h h')
    exact vr.1 x x' (hR.support x y h).1 (hR.support x' y' h').1 hm er

theorem typed_iso {V W : Type}
    (L : List V) (M : List W) (ndL : L.Nodup) (ndM : M.Nodup)
    (allL : ∀ x : V, x∈L) (allM : ∀ y : W, y∈M)
    (E : V → V → Prop) (F : W → W → Prop)
    (symE : ∀ x y, E x y → E y x) (symF : ∀ x y, F x y → F y x)
    (irE : ∀ x, ¬E x x) (irF : ∀ y, ¬F y y)
    (P : V → Prop) (Q : W → Prop) (p q k : Nat)
    (hE : HasType L E P p q k) (hF : HasType M F Q p q k) :
    IsoOn E F P Q := by
  obtain ⟨r,vr,hp,hq,hk⟩ := hE
  obtain ⟨t,vt,hp',hq',hk'⟩ := hF
  have matchEqE := matched_side_equal L ndL allL E symE r P vr
  have matchEqF := matched_side_equal M ndM allM F symF t Q vt
  change MatchN L E P r true = MatchN L E P r false at matchEqE
  change MatchN M F Q t true = MatchN M F Q t false at matchEqF
  obtain ⟨R,pr⟩ := pairing_exists L M ndL ndM allL allM
    (OnMatch E r P true) (OnMatch F t Q true) (hk.trans hk'.symm)
  obtain ⟨U,pu⟩ := pairing_exists L M ndL ndM allL allM
    (OnUnmatch E r P true) (OnUnmatch F t Q true) (by
      rw [on_unmatch_count,on_unmatch_count,hp,hp',hk,hk'])
  obtain ⟨Z,pz⟩ := pairing_exists L M ndL ndM allL allM
    (OnUnmatch E r P false) (OnUnmatch F t Q false) (by
      rw [on_unmatch_count,on_unmatch_count,hq,hq',←matchEqE,←matchEqF,hk,hk'])
  let C := CrossLR E r P
  let D := CrossLR F t Q
  have pc := cross_pairing E symE r P vr
  have pd := cross_pairing F symF t Q vt
  have comp := pairing_comp (OnMatch E r P false) (OnMatch E r P true)
    (OnMatch F t Q true) (fun x a => C a x) R
    (pairing_symm _ _ C pc) pr
  let S : V → W → Prop := fun x y => ∃ b, (∃ a,C a x ∧ R a b) ∧ D b y
  have ps : Pairing (OnMatch E r P false) (OnMatch F t Q false) S :=
    pairing_comp _ _ _ _ D comp pd
  have pl := pairing_union _ _ _ _ R U pr pu
    (fun x h h' => h'.2.2 h.2.2) (fun x h h' => h'.2.2 h.2.2)
  have pl' : Pairing (fun x => P x ∧ r x=true) (fun y => Q y ∧ t y=true)
      (fun x y => R x y ∨ U x y) :=
    pairing_congr _ _ _ _ _ pl (side_partition E r P true) (side_partition F t Q true)
  have pn := pairing_union _ _ _ _ S Z ps pz
    (fun x h h' => h'.2.2 h.2.2) (fun x h h' => h'.2.2 h.2.2)
  have pn' : Pairing (fun x => P x ∧ r x=false) (fun y => Q y ∧ t y=false)
      (fun x y => S x y ∨ Z x y) :=
    pairing_congr _ _ _ _ _ pn (side_partition E r P false) (side_partition F t Q false)
  let T : V → W → Prop := fun x y => (R x y ∨ U x y) ∨ (S x y ∨ Z x y)
  have pt := pairing_union _ _ _ _ _ _ pl' pn'
    (fun x h h' => by rw [h.2] at h'; exact Bool.noConfusion h'.2)
    (fun y h h' => by rw [h.2] at h'; exact Bool.noConfusion h'.2)
  have pt' : Pairing P Q T := pairing_congr _ _ _ _ _ pt
    (by intro x; cases r x <;> simp)
    (by intro y; cases t y <;> simp)
  refine ⟨T,pt',?_⟩
  intro x x' y y' h h'
  rcases h with hl | hr <;> rcases h' with hl' | hr'
  · have h1 := pl'.support x y hl
    have h2 := pl'.support x' y' hl'
    exact same_side_transport E F r t P Q irE irF vr vt T pt' x x' y y'
      (Or.inl hl) (Or.inl hl') (h1.1.2.trans h2.1.2.symm) (h1.2.2.trans h2.2.2.symm)
  · exact cross_edge_transport E F r t P Q C D R U Z rfl rfl pc pd pr pu pz
      x x' y y' hl hr'
  · have e := cross_edge_transport E F r t P Q C D R U Z rfl rfl pc pd pr pu pz
      x' x y' y hl' hr
    exact ⟨fun h => symF y' y (e.1 (symE x x' h)),
      fun h => symE x' x (e.2 (symF y y' h))⟩
  · have h1 := pn'.support x y hr
    have h2 := pn'.support x' y' hr'
    exact same_side_transport E F r t P Q irE irF vr vt T pt' x x' y y'
      (Or.inr hr) (Or.inr hr') (h1.1.2.trans h2.1.2.symm) (h1.2.2.trans h2.2.2.symm)

#print axioms typed_iso


theorem pairing_restrict {V W : Type} (P : V → Prop) (Q : W → Prop)
    (A : V → Prop) (B : W → Prop) (R : V → W → Prop)
    (hR : Pairing P Q R)
    (h : ∀ x y, R x y → (A x ↔ B y)) :
    Pairing (fun x => P x ∧ A x) (fun y => Q y ∧ B y)
      (fun x y => R x y ∧ A x) := by
  constructor
  · rintro x y ⟨hxy,ha⟩
    exact ⟨⟨(hR.support x y hxy).1,ha⟩,⟨(hR.support x y hxy).2,(h x y hxy).1 ha⟩⟩
  · rintro x ⟨hx,ha⟩
    obtain ⟨y,hy⟩ := hR.left x hx
    exact ⟨y,hy,ha⟩
  · rintro y ⟨hy,hb⟩
    obtain ⟨x,hx⟩ := hR.right y hy
    exact ⟨x,hx,(h x y hx).2 hb⟩
  · intro x y z hy hz
    exact hR.row x y z hy.1 hz.1
  · intro x y z hx hy
    exact hR.col x y z hx.1 hy.1

noncomputable def transportSide {V W : Type} (R : V → W → Prop)
    (r : V → Bool) (y : W) : Bool :=
  @decide (∃ x,R x y ∧ r x=true) (Classical.propDecidable _)

theorem transportSide_eq {V W : Type} (P : V → Prop) (Q : W → Prop)
    (R : V → W → Prop) (hR : Pairing P Q R) (r : V → Bool)
    (x : V) (y : W) (h : R x y) : transportSide R r y = r x := by
  classical
  cases hr : r x
  · have hn : ¬(∃ z,R z y ∧ r z=true) := by
      rintro ⟨z,hz,he⟩
      have hzx := hR.col z x y hz h
      subst z
      rw [hr] at he
      contradiction
    simp [transportSide,hn]
  · simp [transportSide,show ∃ z,R z y ∧ r z=true from ⟨x,h,hr⟩]

theorem iso_preserves_type {V W : Type}
    (L : List V) (M : List W) (ndL : L.Nodup) (ndM : M.Nodup)
    (allL : ∀ x : V, x∈L) (allM : ∀ y : W, y∈M)
    (E : V → V → Prop) (F : W → W → Prop)
    (P : V → Prop) (Q : W → Prop) (p q k : Nat)
    (hE : HasType L E P p q k) (iso : IsoOn E F P Q) :
    HasType M F Q p q k := by
  obtain ⟨r,vr,hp,hq,hk⟩ := hE
  obtain ⟨R,hR,hEdge⟩ := iso
  let t : W → Bool := transportSide R r
  have hs : ∀ x y, R x y → t y=r x :=
    transportSide_eq P Q R hR r
  have vt : ValidOn F t Q := by
    constructor
    · intro y z hy hz hne he
      obtain ⟨x,hx⟩ := hR.right y hy
      obtain ⟨w,hw⟩ := hR.right z hz
      have hn : x≠w := by intro e; subst w; exact hne (hR.row x y z hx hw)
      have eq : r x=r w := by rw [←hs x y hx,←hs w z hw]; exact he
      exact (hEdge x w y z hx hw).1
        (vr.1 x w (hR.support x y hx).1 (hR.support w z hw).1 hn eq)
    · intro y z u hy hz hu hne hne' e e'
      obtain ⟨x,hx⟩ := hR.right y hy
      obtain ⟨a,ha⟩ := hR.right z hz
      obtain ⟨b,hb⟩ := hR.right u hu
      have hn : r x≠r a := by rw [←hs x y hx,←hs a z ha]; exact hne
      have hn' : r x≠r b := by rw [←hs x y hx,←hs b u hb]; exact hne'
      have he := vr.2 x a b (hR.support x y hx).1 (hR.support a z ha).1
        (hR.support b u hb).1 hn hn' ((hEdge x a y z hx ha).2 e)
        ((hEdge x b y u hx hb).2 e')
      subst b
      exact hR.row a z u ha hb
  have hm : ∀ x y, R x y → (MatchedOn E r P x ↔ MatchedOn F t Q y) := by
    intro x y hxy
    constructor
    · rintro ⟨z,hz,hn,e⟩
      obtain ⟨w,hw⟩ := hR.left z hz
      refine ⟨w,(hR.support z w hw).2,?_,(hEdge x z y w hxy hw).1 e⟩
      rw [hs x y hxy,hs z w hw]; exact hn
    · rintro ⟨w,hw,hn,e⟩
      obtain ⟨z,hz⟩ := hR.right w hw
      refine ⟨z,(hR.support z w hz).1,?_,(hEdge x z y w hxy hz).2 e⟩
      rw [←hs x y hxy,←hs z w hz]; exact hn
  have countS : ∀ u : Bool, SideN L P r u=SideN M Q t u := by
    intro u
    have hPair := pairing_restrict P Q (fun x => r x=u) (fun y => t y=u) R hR
      (by intro x y h; change (r x=u ↔ t y=u); rw [hs x y h])
    exact pairing_count L M ndL ndM allL allM _ _ _ hPair
  have countM : MatchN L E P r true=MatchN M F Q t true := by
    have hPair := pairing_restrict P Q
      (fun x => r x=true ∧ MatchedOn E r P x)
      (fun y => t y=true ∧ MatchedOn F t Q y) R hR
      (by intro x y h; change ((r x=true ∧ MatchedOn E r P x) ↔ (t y=true ∧ MatchedOn F t Q y)); rw [hs x y h,hm x y h])
    exact pairing_count L M ndL ndM allL allM _ _ _ hPair
  exact ⟨t,vt,(countS true).symm.trans hp,(countS false).symm.trans hq,countM.symm.trans hk⟩

theorem type_iff_iso {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V, x∈L) (E : V → V → Prop)
    (symm : ∀ x y,E x y → E y x) (irrefl : ∀ x,¬E x x)
    (P : V → Prop) (p q k : Nat) (hp : k≤p) (hq : k≤q) :
    HasType L E P p q k ↔
      IsoOn E (@cvEdge p q k) P (fun _ => True) := by
  constructor
  · intro h
    exact typed_iso L (cvList p q k) nd (cvList_nd p q k) all (cvList_all p q k)
      E cvEdge symm cvSymm irrefl cvIrrefl P (fun _ => True) p q k h (cvType p q k hp hq)
  · intro h
    exact iso_preserves_type (cvList p q k) L (cvList_nd p q k) nd (cvList_all p q k) all
      cvEdge E (fun _ => True) P p q k (cvType p q k hp hq) (iso_symm _ _ _ _ h)

#print axioms iso_preserves_type
#print axioms type_iff_iso


-- Final public-facing statements use graph isomorphism, not HasType.
noncomputable def IsoCardN {V : Type} (L : List V) (E : V → V → Prop)
    (c k : Nat) : Nat :=
  Count L (fun v => IsoOn E (@cvEdge c (c-1) k) (fun x => x≠v) (fun _ => True))

theorem card_count_iso {V : Type} (L : List V) (nd : L.Nodup)
    (all : ∀ x : V,x∈L) (E : V → V → Prop)
    (symm : ∀ x y,E x y → E y x) (irrefl : ∀ x,¬E x x)
    (c k : Nat) (hk : k≤c-1) :
    CardN L E c k = IsoCardN L E c k := by
  apply count_congr
  intro v _
  exact type_iff_iso L nd all E symm irrefl (fun x => x≠v) c (c-1) k (by omega) hk

def IsoBlock (b s a d : Nat) : Prop :=
  ∃ (V : Type) (L : List V) (E : V → V → Prop),
    L.Nodup ∧ (∀ x : V,x∈L) ∧ (∀ x y,E x y → E y x) ∧
    (∀ x,¬E x x) ∧ L.length=2*(b+s) ∧
    ¬IsoOn E (@cvEdge (b+s) (b+s) b) (fun _ => True) (fun _ => True) ∧
    a≤IsoCardN L E (b+s) (b-1) ∧ d≤IsoCardN L E (b+s) b

theorem iso_block_equiv (b s a d : Nat) (hs : 1≤s) :
    IsoBlock b s a d ↔ GraphBlock b s a d := by
  constructor
  · rintro ⟨V,L,E,nd,all,sy,ir,hlen,nt,ha,hd⟩
    have et := type_iff_iso L nd all E sy ir (fun _ => True) (b+s) (b+s) b (by omega) (by omega)
    have ea := card_count_iso L nd all E sy ir (b+s) (b-1) (by omega)
    have eb := card_count_iso L nd all E sy ir (b+s) b (by omega)
    rw [←ea] at ha
    rw [←eb] at hd
    exact ⟨V,L,E,nd,all,sy,ir,hlen,fun h => nt (et.1 h),ha,hd⟩
  · rintro ⟨V,L,E,nd,all,sy,ir,hlen,nt,ha,hd⟩
    have et := type_iff_iso L nd all E sy ir (fun _ => True) (b+s) (b+s) b (by omega) (by omega)
    have ea := card_count_iso L nd all E sy ir (b+s) (b-1) (by omega)
    have eb := card_count_iso L nd all E sy ir (b+s) b (by omega)
    rw [ea] at ha
    rw [eb] at hd
    exact ⟨V,L,E,nd,all,sy,ir,hlen,fun h => nt (et.2 h),ha,hd⟩

theorem identifying_subdeck_iff (b s a d : Nat)
    (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    IsoBlock b s a d ↔ Blocked b s a d :=
  (iso_block_equiv b s a d hs).trans (graph_block_iff b s a d hb hs hc)

theorem canonical_deck (b s : Nat) (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    IsoCardN (cvList (b+s) (b+s) b) (@cvEdge (b+s) (b+s) b) (b+s) (b-1)=2*b ∧
    IsoCardN (cvList (b+s) (b+s) b) (@cvEdge (b+s) (b+s) b) (b+s) b=2*s ∧
    ∀ v : CV (b+s) (b+s) b,
      IsoOn (@cvEdge (b+s) (b+s) b) (@cvEdge (b+s) (b+s-1) (b-1)) (fun x => x≠v) (fun _ => True) ∨
      IsoOn (@cvEdge (b+s) (b+s) b) (@cvEdge (b+s) (b+s-1) b) (fun x => x≠v) (fun _ => True) := by
  let c := b+s
  let L := cvList c c b
  let E := @cvEdge c c b
  have nd : L.Nodup := cvList_nd c c b
  have all : ∀ x,x∈L := cvList_all c c b
  have symm : ∀ x y,E x y → E y x := cvSymm
  have irr : ∀ x,¬E x x := cvIrrefl
  have ty : HasType L E (fun _ => True) c c b := cvType c c b (by omega) (by omega)
  have ea := balanced_profile L nd all E symm c b (b-1) hc ty
  have eb := balanced_profile L nd all E symm c b b hc ty
  have h0 : b≠b-1 := by omega
  have h1 : b=b-1+1 := by omega
  rw [if_neg h0,if_pos h1] at ea
  rw [if_pos rfl] at eb
  have eai := card_count_iso L nd all E symm irr c (b-1) (by omega)
  have ebi := card_count_iso L nd all E symm irr c b (by omega)
  refine ⟨eai.symm.trans ea,?_,?_⟩
  · change IsoCardN L E c b=2*s
    rw [←ebi,eb]
    omega
  · intro v
    obtain ⟨r,valid,hp,hq,hk⟩ := ty
    by_cases hm : MatchedOn E r (fun _ => True) v
    · left
      apply (type_iff_iso L nd all E symm irr (fun x => x≠v) c (c-1) (b-1) (by omega) (by omega)).1
      exact (balanced_card_iff L nd all E symm r valid c b (b-1) hc hp hq hk v).2 (Or.inl ⟨hm,h1⟩)
    · right
      apply (type_iff_iso L nd all E symm irr (fun x => x≠v) c (c-1) b (by omega) (by omega)).1
      exact (balanced_card_iff L nd all E symm r valid c b b hc hp hq hk v).2 (Or.inr ⟨hm,rfl⟩)

theorem ally_formula (b s : Nat) :
    Ally b s = if s=1 then max 5 (b+s) else min (b+2) (s+3) := by
  unfold Ally
  by_cases h : s=1
  · rw [if_pos h,if_pos h]
    by_cases e : b+s≤5
    · rw [if_pos e,Nat.max_eq_left e]
    · rw [if_neg e,Nat.max_eq_right (by omega)]
  · rw [if_neg h,if_neg h]
    by_cases e : b+2≤s+3
    · rw [if_pos e,Nat.min_eq_left e]
    · rw [if_neg e,Nat.min_eq_right (by omega)]

theorem exact_ally_reconstruction_number (b s : Nat)
    (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    let n := if s=1 then max 5 (b+s) else min (b+2) (s+3)
    (∀ a d, Feasible b s a d → ¬IsoBlock b s a d → n≤a+d) ∧
    (∃ a d, Feasible b s a d ∧ ¬IsoBlock b s a d ∧ a+d=n) := by
  dsimp
  rw [←ally_formula b s]
  obtain ⟨hl,hu⟩ := graph_ally b s hb hs hc
  constructor
  · intro a d hf h
    exact hl a d hf (fun h' => h ((iso_block_equiv b s a d hs).2 h'))
  · obtain ⟨a,d,hf,h,he⟩ := hu
    exact ⟨a,d,hf,fun h' => h ((iso_block_equiv b s a d hs).1 h'),he⟩

theorem exact_adversary_reconstruction_number (b s : Nat)
    (hb : 2≤b) (hs : 1≤s) (hc : 4≤b+s) :
    (∀ a d, Feasible b s a d → a+d=b+s+2 → ¬IsoBlock b s a d) ∧
    (∀ n, n<b+s+2 → ∃ a d, Feasible b s a d ∧ a+d=n ∧ IsoBlock b s a d) := by
  constructor
  · intro a d hf he hi
    have h := blocked_upper b s a d hf ((identifying_subdeck_iff b s a d hb hs hc).1 hi)
    omega
  · intro n hn
    let a := min b n
    let d := n-a
    have ha : a≤b := Nat.min_le_left _ _
    have han : a≤n := Nat.min_le_right _ _
    have hd : d≤s+1 := by
      dsimp [d,a]
      by_cases h : b≤n
      · rw [Nat.min_eq_left h]; omega
      · rw [Nat.min_eq_right (by omega)]; omega
    refine ⟨a,d,?_,?_,?_⟩
    · unfold Feasible; omega
    · dsimp [d]; omega
    · apply (identifying_subdeck_iff b s a d hb hs hc).2
      exact Or.inr (Or.inr ⟨ha,hd⟩)

#print axioms identifying_subdeck_iff
#print axioms canonical_deck
#print axioms exact_ally_reconstruction_number
#print axioms exact_adversary_reconstruction_number

end CliqueMatching














