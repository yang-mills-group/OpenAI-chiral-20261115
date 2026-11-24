import YM.SU5.WakeInvestment.Contracts
import YM.SU5.WakeInvestment.Tilt

/-!
For integrating the checker Fock numerator. Represent also all the Wick polynomials in the spin
legs here, evaluating at *any given* values of the curl variables in such estimates. Those are
later charges. May use these even at their path-dependent coefficients and expansion supports.
`Lyrics` licenses a root's polynomial estimate (original frame **before** tilt and shear but
**after** any gauge move!). Work in raw site basis. `columnDeal` over all of Single will afford
the sampling in these polynomials. No payments for a Spin trace in a different period.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Set Filter Fock Lattice Finset NormedSpace
open Papyrus Papyrus.Franc
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I] {A B : Op I}
variable {P Q : Op I} {v u E W ε w:ℝ}

abbrev Cage (I : Type*) [LinearOrder I] [Fintype I] := List (Bool × I)
def pitchAct (b : Bool × I) : FC I := Flare.ton (b.1, basisKet b.2)

def textSpin (s:Cage I) := (s.map pitchAct).prod

def useLine (s : List (ℂ × Cage I)) : FC I := (s.map (fun q => q.1 • textSpin q.2)).sum

/-- Root Wakener permission. (WA.6–7 will inspect polynomial on curl terms too when paying mixed
charges; this one in the fiber, payable **after** the SU-gauge move has even acted in Spine.)
`s` all its actual combined gauge-body permission on *Single*, may use *all* slots at each matter
site in those footprints. Not buying the layout conditions here. -/
def Lyrics (s : Finset I) (n : ℕ) (E : ℝ) (F : FC I) : Prop :=
  ∃ l : List (ℂ × Cage I), useLine l=F ∧ (l.map (fun z => ‖z.1‖)).sum ≤ E ∧
    ∀ z∈l, z.2.length ≤ n ∧ ∀ i∈z.2, i.2 ∈ s

def mount (S : Shaft I)(b:Bool): Op I:= if b then star S.buy else S.sell

def swingLeg (S : Shaft I)(x:Bool×I): Leg I:= (x.1, acts (mount S x.1) (basisKet x.2))
lemma beaming (S : Shaft I)(x:Bool×I): S.glow (pitchAct x)=Flare.ton (swingLeg S x):=by
  obtain ⟨b,p⟩:= x; cases b
  · exact S.glow_up _
  exact S.glow_down _
lemma beaming_prod (S:Shaft I)(l:Cage I): S.glow (textSpin l)=loads (l.map (swingLeg S)):=by
  induction l with
  | nil=> exact S.glow_nil
  | cons i l h=>
    change S.glow (pitchAct i*textSpin l)=Flare.ton (swingLeg S i)*loads _
    rw [S.glow_mult,beaming,h]

structure Quotes (S:Shaft I)(v:ℝ) : Prop where
  up: ColumnDeal S.sell v
  down: ColumnDeal (star S.buy) v
lemma Quotes.mount (S:Shaft I)(h:Quotes S v)(b:Bool): ColumnDeal (mount S b) v := by
  cases b; exact h.up; exact h.down

lemma norm_use (S:Shaft I)(l:Cage I)(v:ℝ)(u:1 ≤ v)(t:Quotes S v)(n:ℕ)(p:l.length≤n) : ‖S.glow (textSpin l)‖ ≤ v^n:=by
  rw [beaming_prod]; refine load_price _ _ u ?_ n (by simpa using p)
  intro a e; obtain ⟨b,_,rfl⟩:=List.mem_map.mp e; exact (Quotes.mount _ t b.1).all _

-- Support in tilted comparison estimates via any approximation satisfying measured cost
structure Pillow (S T:Shaft I)(v w:ℝ): Prop where
  flare (b:Bool): ColumnDeal (mount S b - mount T b) w
  pose (b:Bool): ‖mount T b‖ ≤ v
variable (x y:Wave I)

-- Actual Gram with approximation used only in bounding component vectors.
def meeting (x: Wave I)(P:Op I)(T:Shaft I)(i:I) : ℝ := both x P (acts T.sell (basisKet i)) + both x P (acts (star T.buy) (basisKet i))
def tall (x:Wave I)(P:Op I)(T:Shaft I)(s:Finset I) := Real.sqrt (∑ i∈s, meeting x P T i)
lemma meeting_nb (P:Op I)(T:Shaft I)(i:I):0 ≤ meeting x P T i:= add_nonneg (both_ge ..) (both_ge ..)
lemma ponds (p : IsStarProjection P)(T:Shaft I) {S:Shaft I}(h:Pillow S T v w) :
    ∑ i, meeting x P T i ≤ (v^2+v^2)*heatCost x P := by
  rw [add_mul]; exact (by unfold meeting; rw [sum_add_distrib]; exact add_le_add (wakeBessel x p T.sell v (h.pose false)) (wakeBessel x p (star T.buy) v (h.pose true)))
variable [Nonempty I] {s: Finset I}
local notation "Λ" => tiltBound
private lemma crownDiff (A B:Op I)(e:ColumnDeal (A-B) v)(i:I)(y:Op I)(t:IsStarProjection y)(b:Bool) :
    let f(V:Op I):= acts (creed b (acts y (acts V (basisKet i)))) x; ‖f A - f B‖ ≤ v*‖x‖:=by
  intro f
  have he: f A-f B = f (A-B) := by
    unfold f; rw [←act_sub,act_sub A,map_sub];
    cases b <;> simp [creed,Fock.remove]
  rw [he]; apply (paid_normW ..).trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (Flare.cost_pe ..).trans ((proj_cap t _).trans (e.all i))

lemma permits_both (S T:Shaft I)(p:IsStarProjection Q) (t:Pillow S T u ε)(b:Bool)(i:I)(a:i∈ s):
    let V:=acts (mount S b) (basisKet i); let d:= tall x Q T s + ε*‖x‖
    ‖acts (create (acts Q V)) x‖ ≤ d ∧ ‖acts (Fock.remove (acts (1-Q) V)) x‖ ≤ d:=by
  intro V d; let V':=acts (mount T b) (basisKet i)
  have hv: both x Q V' ≤ ∑ i∈s, meeting x Q T i:=by
    apply le_trans _ (single_le_sum (f:=meeting x Q T) (fun j _=>meeting_nb x _ _ j) a); unfold meeting
    cases b; exact le_add_of_nonneg_right (both_ge ..); exact le_add_of_nonneg_left (both_ge ..)
  have ht:‖acts (create (acts Q V')) x‖ ≤ tall x Q T s:= Real.le_sqrt_of_sq_le ((le_add_of_nonneg_left (sq_nonneg _)).trans hv)
  have hV: ‖acts (Fock.remove (acts (1-Q) V')) x‖ ≤ tall x Q T s:= Real.le_sqrt_of_sq_le ((le_add_of_nonneg_right (sq_nonneg _)).trans hv)
  constructor
  · let L(u:Ket I):= acts (create (acts Q u)) x
    change ‖L V‖≤ tall x Q T s + ε*‖x‖
    exact (norm_le_norm_sub_add (L V) (L V')).trans ((add_le_add (crownDiff x _ _ (t.flare b) i Q p false) ht).trans_eq (add_comm ..))
  let L(u:Ket I):= acts (Fock.remove (acts (1-Q) u)) x
  change ‖L V‖≤ tall x Q T s + ε*‖x‖
  exact (norm_le_norm_sub_add (L V) (L V')).trans ((add_le_add (crownDiff x _ _ (t.flare b) i _ p.one_sub true) hV).trans_eq (add_comm ..))

variable {n:ℕ} {F : FC I} (S T:Shaft I)

private noncomputable def glowLin (S:Shaft I): FC I →ₗ[ℂ] FC I where
  toFun:= S.glow
  map_add':= S.glow_sum
  map_smul':= S.glow_free

omit [Nonempty I] in
lemma spend_lyrics {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X] (f: FC I →ₗ[ℂ] X) (h: Lyrics s n E F) {z:ℝ} (p: 0 ≤ z) (g:∀ (L:Cage I), L.length ≤ n→(∀ i∈L,i.2∈s)→‖f (textSpin L)‖≤z): ‖f F‖ ≤ E*z:=by
  obtain ⟨l,rfl,a,b⟩:= h
  apply le_trans _ (mul_le_mul_of_nonneg_right a p); clear a
  induction l with
  | nil=>simp [useLine]
  | cons i l ih=>
    change ‖f (i.1 • textSpin i.2 + useLine l)‖ ≤ _
    rw [map_add,map_smul]; apply (norm_add_le ..).trans; rw [norm_smul]; simp only [List.map_cons,List.sum_cons,add_mul];
    obtain ⟨u,v⟩:= b i List.mem_cons_self
    exact add_le_add (mul_le_mul_of_nonneg_left (g _ u v) (norm_nonneg _)) (ih (fun i h=> b i (List.mem_cons_of_mem _ h)))

omit [Nonempty I] in
lemma Lyrics.post (q: Quotes S v)(h:1 ≤ v)(c:Lyrics s n E F) : ‖S.glow F‖≤ E*v^n :=
  spend_lyrics (glowLin S) c (pow_nonneg (zero_le_one.trans h) _) (fun l p _=> norm_use S l v h q n p)

lemma Lyrics.grain (p: IsStarProjection Q) (h:Quotes S v) (a:1 ≤ v) (c: Sea Q y)
    (z:Pillow S T u ε) (e:0≤ ε) (r:Lyrics s n E F) :
    ‖discrepancy x y (S.glow F)‖ ≤ E*(‖x‖*(tall x Q T s + ε*‖x‖)*wordToll v n) := by
  let W := tall x Q T s + ε*‖x‖; have hw:0 ≤ W:= add_nonneg (Real.sqrt_nonneg _) (mul_nonneg e (norm_nonneg _));
  refine spend_lyrics ((discrepancy x y).comp (glowLin S)) r (mul_nonneg (mul_nonneg (norm_nonneg _) hw) (prance (zero_le_one.trans a) _)) ?_
  intro l hp hz; change ‖discrepancy x y (S.glow _)‖≤_
  rw [beaming_prod]; apply probe_diff x y Q p c _ v W a hw _ (by simpa using hp)
  · rintro i H; obtain ⟨i,_,rfl⟩:=List.mem_map.mp H; exact (Quotes.mount _ h i.1).all _
  intro i H; obtain ⟨i,m,rfl⟩:= List.mem_map.mp H; exact permits_both x S T p z _ _ (hz i m)

/-- Poised for RA Rank work: a per-root Young budget version of (WA.11).
Strength cost one for energy absorption over all roots, *not* per root. -/
lemma entire_lyrics {J:Type*} [Fintype J] (σ:J→ Finset I)(o:Set.PairwiseDisjoint Set.univ σ) (p:IsStarProjection Q) (c:Sea Q y)(F:J→ FC I)(a:0 ≤ E)(w:∀ i,Lyrics (σ i) n E (F i)) (z:Pillow S T u ε)(b:0≤ε)(g:Quotes S v)(f:1 ≤ v):
    ∑ i, ‖discrepancy x y (S.glow (F i))‖ ≤ heatCost x Q + (Fintype.card J)*((u^2+u^2)*(E*wordToll v n)^2 + ε*E*wordToll v n)*‖x‖^2 := by
  classical
  let K:=Fintype.card J; let ω:= u^2+u^2; let i' := E*wordToll v n
  let d:= heatCost x Q; let s:= tall x Q T ∘ σ; let m:= ∑ i, s i
  have hd:0≤d:=heat_nonneg x p; have h0:0≤ i':=mul_nonneg a (prance (zero_le_one.trans f) n)
  have hp:0≤ω:=add_nonneg (sq_nonneg _) (sq_nonneg _); have hu i : 0 ≤ s i := Real.sqrt_nonneg _
  have hz: ∑ i, s i ^ 2 ≤ ω*d:= by
    let U:= meeting x Q T
    have hh: ∑ i∈ (univ.biUnion σ), U i ≤ ∑ i, U i := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>meeting_nb x _ _ _)
    have H(i):s i^2 = ∑ j∈ σ i,U j:=Real.sq_sqrt (sum_nonneg fun i _=> meeting_nb x _ _ _)
    simp_rw [H,←sum_biUnion (s:=univ) (t:=σ) (by simpa using o)]
    exact hh.trans (ponds x p T z)
  have hs: m^2 ≤ K*(ω*d) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg (α:=ℝ) K))
    simpa [m,K] using (sum_mul_sq_le_sq_mul_sq univ (fun (_:J)=> (1:ℝ)) s)
  let t:= (K:ℝ)*ω*i'^2*‖x‖^2
  have ht:0≤t:=by unfold t; positivity
  have hr: i'*‖x‖*m ≤ d+t:=by
    apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
    rw [mul_pow (i'*‖x‖)]; refine le_trans (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) ?_
    rw [show (i'*‖x‖)^2*(K*(ω*d))=t*d from (by unfold t; ring)]
    nlinarith only [sq_nonneg t,sq_nonneg d,mul_nonneg ht hd]
  refine (sum_le_sum (fun i _=>Lyrics.grain x y S T p g f c z b (w i))).trans ?_
  simp_rw [show ∀ j, E * (‖x‖ * (tall x Q T (σ j) + ε * ‖x‖) * wordToll v n) = i'*‖x‖*s j + ε * E * wordToll v n * ‖x‖^2 from (fun j=> by unfold s i'; simp only [Function.comp_apply]; ring)]
  rw [sum_add_distrib, ←mul_sum, sum_const, nsmul_eq_mul, card_univ]; apply (add_le_add_left hr _).trans; exact le_of_eq (by unfold d t i' K ω; ring)

#print axioms entire_lyrics
end YM.CF.WakeInvestment
