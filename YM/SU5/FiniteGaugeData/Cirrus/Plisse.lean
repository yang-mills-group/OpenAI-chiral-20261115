import YM.SU5.FiniteGaugeData.Cirrus.Fenetre
set_option autoImplicit false
set_option maxHeartbeats 55000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison
open Mink Mink.General Vp.Folio
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)(o:‖Ω.val‖=1)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)
local notation "a"=>timeAxis
variable {n:ℕ} (x:Points n)(e:Cross a) (u:Fin n→ℝ) (w:Fin n→G.Chip) (L: List (Fin n))(b:Shelf S e)
local notation "F"=> foil S e b
local notation "A"=>G.Sr S Ω
abbrev angled (r:ℝ):= points fun i=> x i+(r*u i)• e.val
variable (r:ℝ)
local notation "P"=> angled x e u
local notation "χ"=> clockV a x
private abbrev fiat(i j:Fin n):=OS.Semigroup.duration ((χ j-χ i).toNNReal)
private abbrev αu (q:ℂ)(i j:Fin n):= q * (↑(u j-u i):ℂ)
private abbrev βu (q:ℝ)(i j:Fin n):= q * (u j-u i)
private abbrev spaceX(x:Points n)(i:Fin n):=(SEP a (x i)).val
lemma hspace(i:Fin n): spaceX (P r) i=spaceX x i+(r*u i) • e.val:=by
 let t:= e.val; have he:t a=0:= e.property; simp only [angled, spaceX, points_apply, map_add, map_smul]; change _ + _ =_ + _ -- use Submodule coe
 rw [show SEP a e.val=e from Subtype.ext (show t-t a • basis a=t from by rw [he, zero_smul,sub_zero])]; rfl
lemma hclock: clockV a (P r)=clockV a x:=by
 funext i; simp [clockV,angled]; exact Or.inr e.property
private abbrev Uₗ (i j:Fin n):= G.credit w i+G.credit w j
private def spring(q:ℂ)(i j:Fin n) : H.Op:= F (Uₗ G w i j) (fiat x i j) (αu u q i j) * M S (spaceX x j-spaceX x i)
private def τ(x:Points n)(i j:Fin n):H.Op:= M S (-spaceX x i) * rho S (G.credit w) (clockV a x) i j * M S (spaceX x j)
lemma trackH(i j:Fin n)(p:χ i<χ j): spring S G x e u w b r i j= τ S G w (P r) i j:=by
 let k:= Uₗ G w i j; let z:=fiat x i j; have ht: z∈OS.Semigroup.inside:= dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr p))
 let t:= βu u r i j; rw [spring, show αu u r i j=(t:ℂ) from (by unfold αu t βu; push_cast; rfl),realF S e b _ _ _ ht, albe, ← laneslot]; unfold τ; rw [hclock]; let f(r:ℝ):=P r; let K:= parabola S k z; let T:=M S; let W(i):=spaceX x i; let p'(j:Fin n):=spaceX (P r) j
 change K * T (t • e.val) * T (W j-W i)= T (-p' i) *K* T (p' j); rw [← show K * T (-p' i)= T (-p' i)*K from mslot S (-p' i) z ht k, mul_assoc,mul_assoc]; unfold T; rw [tgo,tgo]; congr 2; unfold W p'; rw [hspace,hspace]; unfold t βu; rw [mul_sub, sub_smul]; abel
lemma springhol(i j:Fin n)(p:χ i<χ j): AnalyticAt ℂ (fun z=>spring S G x e u w b z i j) (r:ℂ):=by
 apply AnalyticAt.mul (hol_whole S e b (Uₗ G w i j) (r:ℂ) (fun _=> fiat x i j) (fun q=>αu u q i j) analyticAt_const (analyticAt_id.mul analyticAt_const) _) analyticAt_const
 unfold Wheel Shelf₀; change |(αu u r i j).im|<_; simp only [αu, mul_im,ofReal_im,mul_zero,zero_mul,add_zero,abs_zero]; exact dur.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr p))
-- all-path
local notation "Z"=> spring S G x e u w b
local notation "μ"=> G.senses w
private lemma journey_eq {α:Type}{E:Type}[Monoid E](L:List α)(U:α→E)(g h:α→α→E)(p:α→ ℝ)(k:Sau p L)(z:∀ i j,p i<p j→ g i j=h i j): Film U g L=Film U h L:=by
 induction L with
 | nil=> rfl
 | cons i L ih=>
    obtain ⟨v,K⟩:= List.pairwise_cons.mp k; have hs: clip g i L=clip h i L:= by cases L with | nil=> rfl | cons j L=> exact z i j (v _ List.mem_cons_self)
    exact congrArg (fun y=> U i*y) (congrArg₂ (·*·) hs (ih K))
lemma sprang(p:ProofOrder x a L): Film (G.senses w) (Z r) L= Film (μ) (τ S G w (P r)) L:=by
 exact journey_eq L _ _ _ χ p (trackH S G x e u w b r)
lemma springH (p:ProofOrder x a L): AnalyticAt ℂ (fun z=> Film (μ) (Z z) L) (r:ℂ):=by
 induction L with
 | nil=> exact analyticAt_const
 | cons i L ih=> obtain ⟨p,h⟩:=List.pairwise_cons.mp p; simp_rw [Film_step]; apply AnalyticAt.mul analyticAt_const (AnalyticAt.mul _ (ih h)); cases L with | nil=> exact analyticAt_const | cons j L=> exact springhol S G x e u w b r i j (p _ List.mem_cons_self)
private abbrev Κ (z:ℂ) := inner ℂ Ω.val (Film (μ) (Z z) L Ω.val)
include hΩ b
lemma meanMoves(p:ProofOrder x a L) : AnalyticAt ℝ (fun r=> G.Sr S Ω (P r) w L) r:=by
 let V:= Κ S Ω G x e u w L b; let h(r:ℝ): A (P r) w L=V r:=by
    let f(i):=spaceX (P r) i; let B:=rho S (G.credit w) (clockV a (P r)); unfold V Κ; rw [sprang S G x e u w L b r p]; exact twists S Ω.val (μ) B f hΩ L
 have hz:(fun r:ℝ=>V r)=(fun r=>A (P r) w L):=funext fun r=>(h r).symm
 rw [← hz]; have hp:AnalyticAt ℂ V (r:ℂ):= ((innerSL ℂ Ω.val).comp (ContinuousLinearMap.apply ℂ H.space Ω.val)).analyticAt _ |>.comp (springH S G x e u w L b r p); exact (AnalyticAt.restrictScalars (𝕜:=ℝ) hp).comp (Complex.ofRealCLM.analyticAt _)
#print axioms meanMoves
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
