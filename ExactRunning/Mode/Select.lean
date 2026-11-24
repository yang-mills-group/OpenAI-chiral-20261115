import ExactRunning.Mode.Pack
/-! # Mapping external profiles -/
set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m : Side}

-- Pullback by arbitrary linear maps.
lemma beat_comp {f : Corn β → ℝ}
    (L : Corn α →L[ℝ] Corn β) (T : Phase α →ₗ[ℂ] Phase β) (ht : ∀ v,T (axes v)=axes (L v))
    (h : ContDiffAt ℝ ω f 0) (n : ℕ) (v : Fin n → Phase α) :
    beat (f ∘ L) 0 n v = beat f 0 n (T ∘ v) := by
  let H := (beat f 0 n).compLinearMap (fun _ => T)
  refine chordal (F:=beat _ _ _) (M:=H) (Leads.pulse _) (Leads.pulse H) (fun u => ?_) v
  dsimp only [H, MultilinearMap.compLinearMap_apply]
  rw [beat_real,wired L (by rw [map_zero]; exact h.analyticAt),map_zero]
  simp_rw [Function.comp_apply,ht]
  exact (beat_real ..).symm

lemma art_comp {κ : Type} {u : Corn β → Matrix ι κ ℝ}
    (L : Corn α →L[ℝ] Corn β) (T : Phase α →ₗ[ℂ] Phase β) (ht : ∀ v,T (axes v)=axes (L v))
    (h : Memo u 0) (n : ℕ) (v : Fin n → Phase α) :
    art (u ∘ L) n v = art u n (T ∘ v) := by
  ext a b; exact beat_comp L T ht (h a b) n v

variable {κ : Type}

lemma seat_z {u : Corn α → Matrix ι κ ℝ} : seat u 0 = 0 := by
  ext a b; exact (beat (fun z => u z a b) 0 1).map_coord_zero (i:=(0:Fin 1)) (by rfl)
lemma cart_z₁ {u : Corn α → Matrix ι κ ℝ} (p) : cart u 0 p = 0 := by
  ext a b; exact (beat (fun z => u z a b) 0 2).map_coord_zero (i:=(0:Fin 2)) (by rfl)
lemma cart_z₂ {u : Corn α → Matrix ι κ ℝ} (p) : cart u p 0 = 0 := by
  ext a b; exact (beat (fun z => u z a b) 0 2).map_coord_zero (i:=(1:Fin 2)) (by rfl)

section selector
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def segue (sel : ι → Option κ) (F : Film κ α β) : Film ι α β where
  tab := F.tab
  spot i := match sel i with
    | none => 0
    | some k => F.spot k
  arch i j := match sel i, sel j with
    | some k,some l => F.arch k l
    | _,_ => 0

lemma segue.green {F : Film κ α β} {w : ℝ} (h : Play F w) (sel : ι → Option κ) :
    Play (segue sel F) w := by
  constructor
  · exact h.tab
  · intro i; simp only [segue]; split
    · exact (Play.current (ι:=ι) (K:=F.tab) h.tab).spot i
    exact h.spot _
  · intro i j; simp only [segue]; split
    · exact h.arch _ _
    exact (Play.current (ι:=ι) h.tab).arch i j

def optionalRelay (p : Site m) : Option κ → Phase (Co m κ)
  | none => 0
  | some i => relay p i

lemma segue.loads (sel : ι → Option κ)
    {L : Corn (Co m ι) →L[ℝ] Corn (Co m κ)}
    (T : Phase (Co m ι) →ₗ[ℂ] Phase (Co m κ)) (ht : ∀ v,T (axes v)=axes (L v))
    (hr : ∀ p i, T (relay p i) = optionalRelay p (sel i))
    {F : Film κ α β} {u : OperatorF κ m α β} (h : Ticket F u) :
    Ticket (segue sel F) (u ∘ L) := by
  constructor
  · intro i j; exact
      ContDiffAt.comp (f:=L) 0
        (show ContDiffAt ℝ ω (fun z => u z i j) (L 0) from (map_zero L).symm ▸ h.finance i j)
        (L.contDiff.contDiffAt)
  · unfold cardM; rw [Function.comp_apply,map_zero]; exact h.tab
  · intro i p q a
    unfold seat; rw [art_comp L T ht h.finance,
      show T ∘ ![relay p i] = ![optionalRelay p (sel i)] from funext fun j => by fin_cases j; exact hr ..]
    simp only [segue]
    cases sel i
    · rw [show art u 1 ![optionalRelay (κ:=κ) p none] = 0 from seat_z]; exact Jaunt.zero _
    exact h.spot _ _ _ a
  intro i j p q r s a b
  unfold cart; rw [art_comp L T ht h.finance,
    show T ∘ ![relay p i,relay q j] = ![optionalRelay p (sel i),optionalRelay q (sel j)]
      from funext fun k => by fin_cases k <;> exact hr ..,← cart]
  simp only [segue]
  cases sel i
  · simp only [optionalRelay]; rw [cart_z₁]; cases sel j <;> exact Jaunt.zero _
  cases sel j
  · simp only [optionalRelay]; rw [cart_z₂]; exact Jaunt.zero _
  exact h.arch _ _ _ _ _ _ a b

end selector

abbrev Duet (α : Type) := α ⊕ α

namespace Pairing

section alg
variable {R : Type} [Semiring R]

def left : (α⊕β → R) →ₗ[R] α → R :=
  LinearMap.pi fun i => LinearMap.proj (Sum.inl i)
def right : (α⊕β → R) →ₗ[R] β → R :=
  LinearMap.pi fun i => LinearMap.proj (Sum.inr i)

def mix : ((α → R) × (β → R)) →ₗ[R] α ⊕ β → R where
  toFun x := Sum.elim x.1 x.2
  map_add' _ _ := by ext (a|a) <;> rfl
  map_smul' _ _ := by ext (a|a) <;> rfl

def top (β : Type) : (Co m (α⊕β) → R) →ₗ[R] Co m α → R :=
  LinearMap.pi fun i => LinearMap.proj (i.1,Sum.inl i.2)
def bot (α : Type) : (Co m (α⊕β) → R) →ₗ[R] Co m β → R :=
  LinearMap.pi fun i => LinearMap.proj (i.1,Sum.inr i.2)
def tie : ((Co m α → R) × (Co m β → R)) →ₗ[R] Co m (α ⊕ β) → R where
  toFun x := fun i => Sum.elim (fun a => x.1 (i.1,a)) (fun b => x.2 (i.1,b)) i.2
  map_add' _ _ := by ext ⟨_,a|a⟩ <;> rfl
  map_smul' _ _ := by ext ⟨_,a|a⟩ <;> rfl
end alg

@[simp] lemma mix_left (u : Phase α × Phase β) : left (mix u) = u.1 := rfl
@[simp] lemma mix_right (u : Phase α × Phase β) : right (mix u) = u.2 := rfl

lemma left_axes (u : Corn (Co m (α⊕β))) : top β (axes u)= axes (top β u) := rfl
lemma right_axes (u : Corn (Co m (α⊕β))) : bot α (axes u)= axes (bot α u) := rfl
lemma left_tune (v : Phase (α⊕β)) (p : Site m) :
    top β (tune p v) = tune p (left v) := rfl
lemma right_tune (v : Phase (α⊕β)) (p : Site m) :
    bot α (tune p v) = tune p (right v) := rfl

lemma axes_tie (u : Corn (Co m α)) (v : Corn (Co m β)) :
    axes (tie (u,v)) = tie (axes u, axes v) := by ext ⟨_,a|a⟩ <;> rfl
lemma tune_mix (u : Phase α) (v : Phase β) (p : Site m) :
    tune p (mix (u,v)) = tie (tune p u, tune p v) := by ext ⟨_,a|a⟩ <;> rfl

/-- native coarse profiles -/
abbrev first (m) (β : Type) [Fintype β] : Corn (Co m (α⊕β)) →L[ℝ] Corn (Co m α) :=
  LinearMap.toContinuousLinearMap (top β)
abbrev second (m) (α : Type) [Fintype α] : Corn (Co m (α⊕β)) →L[ℝ] Corn (Co m β) :=
  LinearMap.toContinuousLinearMap (bot α)

abbrev zipper (m) (α β : Type) [Fintype α] [Fintype β] :
    Corn (Co m α) × Corn (Co m β) →L[ℝ] Corn (Co m (α ⊕ β)) :=
  LinearMap.toContinuousLinearMap tie

@[simp] lemma first_zipper (z : Corn (Co m α) × Corn (Co m β)) :
    first m β (zipper m α β z) = z.1 := rfl
@[simp] lemma second_zipper (z : Corn (Co m α) × Corn (Co m β)) :
    second m α (zipper m α β z) = z.2 := rfl

lemma tie_repeats {D : Latitude} {u : Corn (Co m α)} {v : Corn (Co m β)}
    (h : D.repeats u) (k : D.repeats v) : D.repeats (zipper m α β (u,v)) := by
  ext ⟨j,x|x⟩
  · exact congr_fun h (j,x)
  exact congr_fun k (j,x)

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma selectL {F : Film ι α β} {u : OperatorF ι m α β} (h : Ticket F u) :
    Ticket (segue (Sum.elim some (fun _ => none)) F) (u ∘ first m κ) := by
  refine segue.loads _ _ left_axes ?_ h
  intro p i
  ext ⟨k,j⟩
  change relay p i (k,.inl j) = _
  cases i <;> simp [optionalRelay,relay,tune,Pi.single_apply]

lemma selectR {F : Film κ α β} {u : OperatorF κ m α β} (h : Ticket F u) :
    Ticket (segue (Sum.elim (fun _ => none) some) F) (u ∘ second m ι) := by
  refine segue.loads _ _ right_axes ?_ h
  intro p i
  ext ⟨k,j⟩
  change relay p i (k,.inr j) = _
  cases i <;> simp [optionalRelay,relay,tune,Pi.single_apply]
end Pairing

variable [Fintype ι] [Fintype κ]
open Pairing

namespace Eyes
variable {σ:ℝ} {E : Eye α β} {L : Corn (Co m α) →L[ℝ] Corn (Co m β)}

def lhalf (E : Eye α β) (ι:Type) : Eye (α⊕ι) β := fun p => (E p).comp left
def rhalf (E : Eye α β) (ι:Type) : Eye (ι⊕α) β := fun p => (E p).comp right

lemma turnsL (h : Turns E L) (ι : Type) [Fintype ι] :
    Turns (lhalf E ι) (L.comp (first m ι)) := by
  classical
  obtain ⟨T,t,s⟩ := h.basis
  refine ⟨T.comp (top ι),fun x => t _,fun p q g x => ?_⟩
  rw [LinearMap.comp_apply,left_tune,s p q g]
  rfl

lemma turnsR (h : Turns E L) (ι : Type) [Fintype ι] :
    Turns (rhalf E ι) (L.comp (second m ι)) := by
  classical
  obtain ⟨T,t,s⟩ := h.basis
  refine ⟨T.comp (bot ι),fun x => t _,fun p q g x => ?_⟩
  rw [LinearMap.comp_apply,right_tune,s p q g]
  rfl

lemma freshL (h : Fresh E σ) (ι : Type) [Fintype ι] :
    Fresh (lhalf E ι) σ where
  shifts hp ht := by dsimp only [lhalf]; rw [h.shifts hp ht]
  sense hh _ := h.sense hh _
lemma freshR (h : Fresh E σ) (ι : Type) [Fintype ι] :
    Fresh (rhalf E ι) σ where
  shifts hp ht := by dsimp only [rhalf]; rw [h.shifts hp ht]
  sense hh _ := h.sense hh _

variable {F : Eye α β} {K : Corn (Co m α) →L[ℝ] Corn (Co m β)}
lemma fresh_add (h : Fresh E σ) (i : Fresh F σ) : Fresh (E+F) σ where
  shifts hp ht := congr_arg₂ (·+·) (h.shifts hp ht) (i.shifts hp ht)
  sense hh x := (h.sense hh x).fun_add (i.sense hh x)

lemma turns_add (h : Turns E L) (i : Turns F K) : Turns (E+F) (L+K) := by
  obtain ⟨T,t,s⟩ := h.basis
  obtain ⟨U,u,r⟩ := i.basis
  refine ⟨T+U,fun x => ?_,fun p q g x => ?_⟩
  · rw [LinearMap.add_apply,t,u]
    ext; exact Complex.ofReal_add .. |>.symm
  rw [LinearMap.add_apply,s p q g,r p q g]
  exact (map_add (tuneL p) ..).symm

lemma fresh_sub (h : Fresh E σ) (i : Fresh F σ) : Fresh (E-F) σ where
  shifts hp ht := congr_arg₂ (·-·) (h.shifts hp ht) (i.shifts hp ht)
  sense hh x := (h.sense hh x).sub (i.sense hh x)

lemma turns_sub (h : Turns E L) (i : Turns F K) : Turns (E-F) (L-K) := by
  obtain ⟨T,t,s⟩ := h.basis
  obtain ⟨U,u,r⟩ := i.basis
  refine ⟨T-U,fun x => ?_,fun p q g x => ?_⟩
  · rw [LinearMap.sub_apply,t,u]
    ext; exact Complex.ofReal_sub .. |>.symm
  rw [LinearMap.sub_apply,s p q g,r p q g]
  exact (map_sub (tuneL p) ..).symm

end Eyes

end ExactRunning
