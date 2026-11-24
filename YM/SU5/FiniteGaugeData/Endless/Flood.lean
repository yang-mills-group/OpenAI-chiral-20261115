import YM.SU5.FiniteGaugeData.Endless.Coin
import YM.SU5.FiniteGaugeData.Mist.Paon
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Endless.Piper
open Function Filter Metric Finset Lattice Hills Mist Complex
open scoped Topology BigOperators InnerProductSpace NNReal
variable {σ:Type} {G H:Hilbert} [DecidableEq σ] {L:Side}{a j:Axis}
open Hike Knot Willow Leda
local notation "𝟙"=> VistaQ L
section
variable (P:Terrace H L a) (Ω:H)(X:σ→H.Op)(A:σ→σ→ H.Op)(S:List σ)(C:List Axis)
def steel(X:σ→H.Op)(i:σ):= planeP (GroupR P C)*X i*planeP (GroupR P C)
abbrev sprocket (C:List Axis) := keep Ω (steel P C X) A S
variable (hp:Ω∈P.Unity)
local notation "P₀"=> planeP (GroupR P C)
variable (p:∀ i j:σ, Commute (A i j) (planeP (GroupR P C)))
-- equality with Coups/inset formulas.
private lemma sponge_P {M Y:H.Op}(h:P₀*M=M) (t:Commute Y P₀) : (P₀)*(Y*M)=Y*M:=Eq.trans (Eq.trans (mul_assoc ..).symm (congrArg (·*M) t.eq.symm)) (Eq.trans (mul_assoc ..) (congrArg (Y*·) h))
include hp p
lemma keep_copes : sprocket P Ω X A S C= keep Ω (coupes P X (fun _=>C)) A S:=by
 have he:= inlet (include_unity _ C hp); let F:=coupes P X (fun _=> C); let V:=steel P C X; have hv(i):V i=P₀*F i:=mul_assoc ..
 have hw:P₀*P₀=P₀:=withdraw (le_refl ..); have hb:(TapeT V A S Ω)=P₀ (TapeT F A S Ω):=by
   cases S with
   | nil=> exact he.symm
   | cons i s=> induction s generalizing i with
     | nil=> change V i Ω=(P₀*F i) Ω; rw [hv]
     | cons j s ih=>
         change V i (A i j (TapeT V A (j::s) Ω))=(P₀*(F i*A i j)) (TapeT F A (j::s) Ω); rw [ih,hv]
         let W:=TapeT F A (j::s) Ω; change (P₀*F i*(A i j*P₀)) W= _; have he: F i*(A i j*P₀)= F i*A i j:= by unfold F coupes; rw [(p i j).eq, ← mul_assoc, mul_assoc (X i) _ P₀,hw]
         exact DFunLike.congr_fun (show P₀*F i*(A i j*P₀)=P₀*(F i*A i j) from (mul_assoc ..).trans (congrArg ((P₀)* ·) he)) W
 change inner ℂ Ω (TapeT V A S Ω)=_; rw [hb, ← planeP_inner, he]; rfl
lemma keepsPrice : sprocket P Ω X A S C = inner ℂ (dip (GroupR P C) Ω) (TapeT (fun i=> social (GroupR P C) (X i)) (fun i j=>social (GroupR P C) (A i j)) S (dip (GroupR P C) Ω)):= Eq.trans (keep_copes P Ω X A S C hp p) (social_chain_price (GroupR P C) Ω X A S p (include_unity _ _ hp))
variable (Y:σ→σ→ H.Op)(b:Axis)
local notation "P₁"=>planeP (Stamina P b)
omit hp p
lemma edition (i:σ): Repairs (steel P C X) (ScrollQ P b) i = steel P (b::C) X i:=by
 unfold steel Repairs; change (P₁)*(P₀*X i*P₀)*(P₁)= _; rw [widget]; have he:= (comm_Group P C (A:=P₁) (fun i=> desk_nick P b i)).eq
 calc _ = (P₁*P₀)* X i * (P₀*P₁):= by simp only [mul_assoc]
      _= _:=by rw [he]
-- keep invariance under travel conjugation on one axis.
include hp
local notation "U" z:max=> ramble P b z
lemma RamFix (r:𝟙):ramble P b r Ω=Ω:=by
 unfold ramble; split; rfl; rename_i g; obtain ⟨n,t,rfl⟩:=(frequentT L r).exists; rw [Driver_eq]; exact (P.unityH ..).1 hp ..
variable (t:σ→ VistaQ L)
lemma transit_P (h:∀ i j, Y i j= ramble P b (-(t i))*A i j*ramble P b (t j)) : keep Ω X Y S=keep Ω (fun i=> faced (ScrollQ P b) (X i) (t i)) A S:=by
 let Q(i:σ):=ramble P b (t i); let N(i:σ):= ramble P b (-(t i)); let Z(i:σ):=faced (ScrollQ P b) (X i) (t i)
 cases S with
 | nil=>rfl
 | cons i s=>
    have hb(s:List σ)(i):TapeT Z A (i::s) Ω=Q i (TapeT X Y (i::s) Ω):=by
         induction s generalizing i with
         | nil=> change Q i (X i (N i Ω))= Q i (X i Ω); rw [show N i Ω=Ω from RamFix P Ω hp b (-(t i))] -- hp tune
         | cons j s ih=> change Z i (A i j (TapeT Z A (j::s) Ω))= Q i (X i (Y i j (TapeT X Y (j::s) Ω))); rw [ih,h]; rfl
    unfold keep; rw [hb]; have hx:= (ScrollQ P b).remain (t i) Ω (TapeT X Y (i::s) Ω); change inner ℂ (Q i Ω) _ =_ at hx; rw [show Q i Ω=Ω from RamFix P Ω hp b _] at hx; exact hx.symm
variable (E:OS.Semigroup H a)(pE:∀ v:VistaQ L,∀ b:Axis,∀ w:ℝ≥0,Commute (E.E w) (ramble P b v))
variable (pQ:∀ b:Axis,∀ w:ℝ≥0,Commute (E.E w) (planeP (Stamina P b)))
variable (x:Grid σ (VistaQ L))(d:σ→ℝ)
def Fog (x:Grid σ (VistaQ L))(b:Axis)(t:σ→ VistaQ L):Grid σ (VistaQ L):=fun i=> x i+Pi.single b (t i)
local notation "pU" => ramble P
local notation "F" u:max=> giro P E d u
omit hp
include pE
lemma fee_foot (z:𝟙)(i j:σ): Commute (giro P E d x i j) (pU b z):= Commute.mul_left (pE z b _) ((glide_group P Terrace.scheduleL (x j-x i) (pU b z) (fun i _=> ramble_across P b i z _)).symm)
include pQ
omit pE in
lemma fee_plane (i j:σ) : Commute (giro P E d x i j) (planeP (GroupR P C)):= Commute.mul_left (comm_Group _ C (pQ · _)) ((glide_group P Terrace.scheduleL (x j-x i) (planeP (GroupR P C)) (fun i _=> (air_Group _ _ _ _).symm)).symm)
omit pQ
lemma shine (g:b≠a)(i j:σ) : (F (Fog x b t)) i j= ramble P b (-(t i))*(F x) i j * ramble P b (t j):= by
 have hp:Fog x b t j-Fog x b t i=x j-x i+Pi.single b (-t i+t j):=by
    ext1 w; by_cases z:w=b; · subst w; simp [Fog]; abel
    simp [Fog,z]
 rw [kettle_p P E d x (Fog x b t) pE i j b _ g hp, ramble_two,mul_assoc, (fee_foot P b E pE x d (t j) i j).eq.symm,← mul_assoc]
include hp
lemma piping(g:b≠a) : keep Ω (steel P C X) (F (Fog x b t)) S= keep Ω (fun i=> faced (ScrollQ P b) (steel P C X i) (t i)) (F x) S := transit_P P Ω (steel P C X) (F x) S hp (F (Fog x b t)) b t (shine P b t E pE x d g)
variable (Q:Terrace G L j)(W:List Axis)(J:OS.Semigroup G j)(pJ:∀ v:VistaQ L,∀ b:Axis,∀ w:ℝ≥0,Commute (J.E w) (ramble Q b v))(vQ:∀ b:Axis,∀ w:ℝ≥0,Commute (J.E w) (planeP (Stamina Q b)))
variable (θ:G)(k:σ→ G.Op)(m:σ→ℝ)(V:List σ)
local notation "u₁" z:max => giro Q J m z
local notation "X'" C:max z:max => sprocket P Ω X (F z) S C
local notation "Z'" C:max z:max => sprocket Q θ k (u₁ z) V C
lemma fee_ξ (i j:σ) : Commute (giro P E d x i j) (planeP (Stamina P b)):= Willow.commute_pay (ScrollQ P b) fun y=>fee_foot P b E pE x d y i j
omit hp pE
include pE pJ hp
variable (hθ:θ∈Q.Unity)(v:S.Nodup)(xv:V.Nodup)
include hθ v xv
lemma sequel (R':Set (ℂ × ℂ))(r:ℝ)(z:0<r)(p:b≠a)(q:b≠j)(h:IsClosed R')(hc: Convex ℝ R')(t:∀ t:σ→VistaQ L, (∀ i, ‖t i‖ < r)→ (X' C (Fog x b t), Z' W (Fog x b t))∈R') : (X' (b::C) x, Z' (b::W) x)∈R':= by
 have he:= quilt Ω (steel P C X) (F x) S v (ScrollQ P b) ((sting P [b] _).1 (include_unity _ [b] hp) _ (by simp)) (fee_ξ P Ω hp b E pE x d) θ (u₁ x) (steel Q W k) V xv (ScrollQ Q b) R' r h hc z ((sting Q [b] _).1 (include_unity Q [b] hθ) _ (by simp)) (fee_ξ Q θ hθ b J pJ x m) (fun w h=> ?_); swap
 · unfold relation; rw [←piping P Ω X S C hp b w E pE x d p,←piping Q θ k V W hθ b w J pJ x m q]; exact t w h
 rw [show Repairs (steel P C X) (ScrollQ P b)=_ from funext (edition P X C b), show Repairs (steel Q W k) (ScrollQ Q b)= _ from funext (edition Q k W b)] at he; exact he
/-  permissible almost stationary unclocked displacements. -/
omit hθ v xv hp pE pJ in
inductive Fare (r:ℝ) : Grid σ (VistaQ L) → List Axis → Grid σ (VistaQ L) → Prop
 | nil(x:Grid σ (VistaQ L)) : Fare r x [] x
 | food(x:Grid σ (VistaQ L))(i:Axis)(B:List Axis)(y: Grid σ (VistaQ L))(t:σ→ VistaQ L)(p:∀ j,‖t j‖<r)(v:Fare r (Fog x i t) B y) : Fare r x (i::B) y
lemma fortunes (R':Set (ℂ × ℂ))(r:ℝ)(z:0<r)(B:List Axis)(p:∀ i∈B,i ≠ a ∧ i≠ j)(h:IsClosed R')(hc:Convex ℝ R')(Ek:∀ y, Fare r x B y → (X' C y,Z' W y)∈R') : (X' (B++C) x,Z' (B++W) x)∈R':=by
 induction B generalizing x with
 | nil=> exact Ek x (.nil _)
 | cons i B ih=>
    obtain ⟨u,m'⟩:=p i (by simp); exact sequel P Ω X S (B++C) hp i E pE x d Q (B++W) J pJ θ k m V hθ v xv R' r z u m' h hc fun t ht=> ih _ (fun j z=> p _ (List.mem_cons_of_mem _ z)) (fun y g=> Ek y (.food x i B y t ht g)) -- order
omit hθ v xv hp pE pJ in
lemma sprocket_p (V:List Axis)(p:GroupR P V=GroupR P C) : sprocket P Ω X A S V = sprocket P Ω X A S C:=by unfold sprocket steel; simp_rw [p]
#print axioms fortunes
end
end YM.CF.Buffered.Afterglow.Hierarchy.Endless.Piper
