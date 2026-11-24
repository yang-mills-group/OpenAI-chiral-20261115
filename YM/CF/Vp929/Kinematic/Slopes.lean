import YM.CF.Pso.Cleft
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
local notation "j'"=> A.loft
local notation "q"=> A.trot
local notation "Q"=> A.LawQ
local notation "L'"=> A.post
local notation "J"=> A.vita
local notation "R"=> A.rota
local notation "v'"=> A.room
local notation "H"=> A.hot
local notation "β"=> A.beta
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "X"=> kist M
variable (f:Sweep (mid N B))(W U': Rent0 G e)(i:Site (Domain N B))
variable {v u:ℝ}(hp1:0<u)(ht':0<v)
local notation "Mt"=> poleY M v u
local notation "Vt"=> tint_z A v
local notation "Ut"=> tint_z A u
local notation "fu"=> M.fuel x T q v' L' u
local notation "fo"=> M.sent x T q v' L' u
local notation "Ξ" t:max=> tint_z A t
local notation "Λ" t:max=> poleY M t u
namespace Firn
/-- Affine slopes in beta; no smoothness in other arguments. -/
def Slopes (f:ℝ→ℂ):Prop:= ∃ a:ℝ, ∃ b:ℂ,∀ x:ℝ,0<x→ f x=(x:ℂ)*a+b
def Line (f:ℝ→ℝ):Prop:=∃ a b:ℝ,∀ x:ℝ,0<x→ f x=x*a+b
variable {p u':ℝ→ℝ}
lemma Line.add (hp:Line p)(ht:Line u'): Line (fun x=>p x+u' x):=by obtain ⟨a,b,h⟩:=hp; obtain ⟨c,d,hQ⟩:=ht; exact ⟨a+c,b+d,fun x vq=> by dsimp only; rw [h x vq,hQ x vq]; ring⟩
lemma Line.sMul (hp:Line p)(t:ℝ): Line (fun x=> t * p x):=by obtain ⟨a,b,h⟩:=hp; exact ⟨t*a,t*b,fun x vq=>by dsimp only; rw [h x vq]; ring⟩
lemma Line.sub (hp:Line p)(ht:Line u'): Line (fun x=>p x-u' x):= by simpa [sub_eq_add_neg] using hp.add (ht.sMul (-1))
lemma Line.sum {Eq1:Type} [DecidableEq Eq1] (Bq:Finset Eq1)(f:Eq1→ℝ→ℝ)(hp:∀ j: Eq1, Line (f j)):Line (fun t=>∑ i∈ Bq,f i t):=by
 induction Bq using Finset.induction_on with
 | empty=> exact ⟨0,0,fun t _=> by simp⟩
 | insert x A hx ih=> simpa [hx] using (hp x).add ih
lemma embed (hp:Line p):Slopes (fun t=>(p t:ℂ)):=by obtain ⟨a,b,h⟩:=hp; exact ⟨a,b,fun t vq=>by dsimp only; rw [h t vq]; push_cast; rfl⟩
variable {Pq Pk:ℝ→ℂ}
lemma Slopes.add (p:Slopes Pq)(vq:Slopes Pk): Slopes (fun t=> Pq t+Pk t):= by obtain ⟨a,b,h⟩:=p; obtain ⟨c,d,hQ⟩:=vq; exact ⟨a+c,b+d,fun t vq=> by dsimp only; rw [h t vq,hQ t vq]; push_cast; ring⟩
lemma Slopes.const(k:ℂ): Slopes (fun _=> k):= ⟨0,k,fun t _=>by simp⟩
lemma Slopes.sMul(p:Slopes Pq)(r:ℝ):Slopes (fun x=> r • Pq x):= by obtain ⟨a,b,h⟩:=p; exact ⟨r*a,r*b,fun t vq=> by dsimp only; rw [h t vq,Complex.real_smul]; push_cast; ring⟩
lemma Slopes.sum {Eq1:Type} [DecidableEq Eq1](Bq:Finset Eq1)(f:Eq1→ℝ→ℂ)(p:∀ i:Eq1, Slopes (f i)):Slopes (fun t=>∑ i∈ Bq,f i t):= by
 induction Bq using Finset.induction_on with
 | empty=> simpa using Slopes.const 0
 | insert x A hx ih=> simpa [hx] using (p x).add ih
lemma Slopes.sign (p:Slopes Pq): Slopes (fun x=>payZ f (Pq x)):= by
 obtain ⟨a,b,h⟩:=p; exact ⟨a,payZ f b, fun t vq=>by dsimp only; rw [h t vq]; unfold payZ; cases wageZ f <;> simp [cSignX]⟩
include A M hp1
private lemma r_line (s:Signed)(k:ℕ)(Va:Palot.leaf (Site (Domain N B)))(i:Site (Domain P B)): Line (fun v=> river (Ξ v) (Λ v) s k Va i):=by
 unfold Muster.river; refine ⟨sapU (Ut) M s k Va i + (extU (Ut) M s k Va i (haste (Stores.till x) T.up.cubic) + extU (Ut) M s k Va i (haste (Stores.till x) T.up.quartic)),extU (Ut) M s k Va i (haste (Stores.till x) T.up.loop),?_⟩; intro v hv; unfold sapU extU; dsimp only [tint_z]; simp_rw [(spirit_X A M hp1 hv).2]; rfl
private lemma f_line (s:Signed)(k:ℕ)(Va:Palot.leaf (Site (Domain N B)))(i:Site (Domain N B)):Line (fun v=> flows (Ξ v) (Λ v) s k Va i):=by
 unfold flows sapC extV; dsimp only [poleY,Cay.rough,tint_z]; exact Line.add ((show Line (fun v:ℝ=>(v+(α+γ))* (sapC A M s k Va i+ (extV A M s k Va i (haste (Stores.till x/S.patch.L.val) T.down.cubic)+extV A M s k Va i (haste (Stores.till x/S.patch.L.val) T.down.quartic)))) from ⟨_,(α+γ)*(sapC A M s k Va i+ (extV A M s k Va i (haste (Stores.till x/S.patch.L.val) T.down.cubic)+extV A M s k Va i (haste (Stores.till x/S.patch.L.val) T.down.quartic))), fun y vq=> add_mul _ _ _⟩).add ⟨0,_,fun x h=>by rw [mul_zero,zero_add]⟩) ⟨0,_,fun x h=> by rw [mul_zero,zero_add]⟩
lemma shard_line (k:ℕ)(Va:Palot.leaf (Site (Domain N B))): Line (fun v=> shardy (Ξ v) (Λ v) k Va):=by
 unfold shardy averaged; simp_rw [← neg_mul]; exact (Line.sum _ _ (fun s=>(Line.sum _ _ (r_line A M hp1 s k Va)).sub (Line.sum _ _ (f_line A M hp1 s k Va)))).sMul _
private lemma mare_s: Slopes (fun v=>Tye.mare (Ξ v) (Λ v) i):= by
 unfold mare patrol; simp_rw [terminal_w A M]; refine (Slopes.sum (univ: Finset (Sweep Z)) _ ?_).sMul _; intro f
 let I:=(chart f).symm i; let m:= Cay.rough (rot f M) 0; let k:= issueC T x m q v' L' j' A.muK A.mup I
 refine Slopes.sign f (Pq:=fun v=> ((-v*k:ℝ):ℂ)- booth A m I) ⟨-k,-booth A m I, fun v h=> by push_cast; ring⟩
lemma mig_s : Slopes (fun v=> mig (Ξ v) (Λ v) W U' i):= by
 have he:Line (fun v=> mix (Ξ v) (Λ v) i):= ⟨u⁻¹*(Muster.wish (Ξ u) M i+flockK (Ξ u) M i),blunt (Ξ u) M i+artU T x q v' L' M i,fun v hv=> by dsimp only; rw [stern_a A M i hp1 hv]; ring⟩
 exact ((embed he).add (Slopes.const (prum A M U' W i))).add (mare_s A M i hp1)
private lemma sore_line(O:Stores S):Line (fun v=>soreG (Ξ v) (Λ v) O):=by
 let g:= averaged (fun s: Signed=>∑ i∈lyn x s O j',Cloak.folkK T x M s q v' L' u A.phaseUp A.phaseLow i)
 let G_:= averaged (fun s:Signed=>∑ i∈strum x s O j',heatR T fo M.V s M.key q A.phaseUp A.phaseLow x (α+γ) i)
 have ht (v:ℝ)(p:0<v):gemG (Ξ v) (Λ v) O=gemG (Ξ u) M O:=by unfold gemG Corne.flare; dsimp only [tint_z]; simp_rw [(spirit_X A M hp1 p).1]; rfl
 have hp(v)(p:0<v): soreG (Ξ v) (Λ v) O=-v*g - G_-gemG (Ξ u) M O:=by
    unfold soreG oak; dsimp only [tint_z]; simp_rw [Cloak.folkK,(spirit_X A M hp1 p).2]; rw [ht v p]; rfl
 exact ⟨-g,-G_-gemG (Ξ u) M O, fun x p=> by dsimp only; rw [hp x p]; ring⟩
lemma hont_s(r k:ℕ)(O:Hos S k):Slopes (fun v=> hont (Ξ v) (Λ v) W U' r k O):=
 (embed (sore_line A M hp1 O.val)).add (Slopes.sum _ _ fun i=> mig_s A M W U' i hp1)
end Firn
end YM.CF.Tye
