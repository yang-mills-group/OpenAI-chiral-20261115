import YM.CF.Corne.Link
import YM.CF.Corne.Falls
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Corne
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reine
local notation "G₅"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r j:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G₅}{P': Tab S}
open Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec Facet Peaks
variable {n' B Mx X: Side}{T: Roam Mx X B}(G: Ratio (CSide Mx B) (CSide X B))(F:Tube G₅ T)
variable {C V R Z η e:ℝ}(Q: Msca Mx X B G e){Φ:nomA Mx X B→ ℂ}
local notation "pG"=> CSide Mx B
local notation "pF"=> CSide X B
local notation "D₀"=> More pG
local notation "D₁"=> More pF
variable (x d u:ℝ)(q:Chi)(l:ℕ)(S: Monk G₅ T)(A:Rent0 G e)(β:ℝ)(t:0 < e)
section
local notation "Y"=> mSeal X B
local notation "k₀"=>(S.park,S.k)
lemma coinI(J:ChartRatio G₅)(v α b w:ℝ)(i:Site D₀):let P(s:ℝ):= Coin F x v q J w d s l k₀ i S.V; P (α+b)= P α+ (P b-P 0):=by
 intro P; unfold P Tarn.Coin; simp only [Pi.sub_apply]; let Y'(a:ℝ):= rugG F x q d a l k₀ i S.V; let M:=MossZ F x q d l J w k₀ i S.V; let N' := neatQ F x v q d l k₀ i S.V
 have h:Y' (α+b)=Y' α+(Y' b-Y' 0):=by
    unfold Y' rugG Arena.aria; simp only [Pi.smul_apply,Finset.sum_apply]; rw [←smul_sub,←smul_add,←sum_sub_distrib,←sum_add_distrib]; apply congrArg ((Fintype.card Signed:ℂ)⁻¹ • ·); apply sum_congr rfl; intro j _; rw [←sum_sub_distrib,←sum_add_distrib]; refine sum_congr rfl fun k _=>?_ ; unfold tilT loreG; rcases k with (i|i|i|i)|i|i <;> simp only [TaleX] <;> push_cast <;> ring
 change Y' _-M-N'=Y' _-M-N'+(Y' _-M-N'-(Y' _-M-N')); rw [h]; abel
abbrev mintB(A:Rent0 G e):= ∑ i∈ (univ.filter fun i:Y=> i.card≤ Stores.till x)ᶜ,Q i A
lemma fond(h:Tally Q Φ u C a Z n):Φ A.val= (∑ i:Site D₀,fJ G Q x A i)+ mintB G Q x A:=by
 rw [h.even A.val A.property, ← sum_add_sum_compl (univ.filter fun i:Y=> i.card≤ Stores.till x)]; congr 1
 unfold fJ; rw [sum_comm]; refine Finset.sum_congr rfl fun i v=>?_ ; rw [←Finset.sum_smul]; obtain ⟨N,H,K⟩:=h.members
 by_cases h:N i=0; rw [show Q i=0 from funext fun x=> norm_le_zero_iff.mp ((H i).sumline _|>.trans_eq h)]; simp
 have ht:i.Nonempty:=by have ht:= (H i).travel h; cases ht<;> simp
 rw [turtle_k _ ht,one_smul]
-- combine Heat uniform and δ physical charge, orientation. old estimation after progress
variable(v b α s e':ℝ)(p j j' r:ℕ)(J:ChartRatio G₅)(A' P₀:Rent0 G e)
local notation "R₀"=>S.key.dome (j*radiusB x)
abbrev posy:= -mintB G Q x A+mintB G Q x P₀
abbrev rockS:= ∑ i∈ R₀,(fJ G Q x P₀ i-fJ G Q x A i)
abbrev pearQ:= ∑ i∈ R₀ᶜ,(fJ G Q x A' i-fJ G Q x A i)
abbrev scenic := posy G Q x A P₀+ rockS G Q x S A j P₀+pearQ G Q x S A j A'
lemma visaS(ηΩ ηΩ': Tab T→DirP (More (CSide Mx B)))(h:Thu F x u l Q t K n η C a Z V R Φ)(p0:P₀.val=(1,1))(hv:∀ i:Site D₀,i∉R₀ → Bride G F x d q l (rough S 0) A' β (radiusB x+1) i ∧ Taurus u S (Cay.horn x l) i)(hx:l+76≤ j):
 -(∑ i∈R₀ᶜ,(Coin F x v q J w d (α+b) l k₀ i S.V))-Φ A.val=scenic G Q x S A j A' P₀ -(∑ i,issued x j p (Coin F x v q J w d α l) ηΩ S.key k₀ i S.V)-(∑ i,issued x j r (snowG G F q x u b d l Q t) ηΩ' S.key k₀ i S.V) -Φ (1,1):=by -- argument w from header
 let S0:= scenic G Q x S A j A' P₀; let X0:=Φ (1,1); let I'(s:ℝ)(i:Site D₀):= Coin F x v q J w d s l k₀ i S.V; let V0(i):= snowG G F q x u b d l Q t k₀ i S.V; let τ(P:Rent0 G e)(i):= fJ G Q x P i
 have hF(Q':Tab _→FileM D₀ G₅)(V:Tab _→ DirP D₀)(k:ℕ):∑ i,issued x j k Q' V S.key k₀ i S.V=∑ i∈R₀ᶜ,Q' k₀ i S.V:=by
    rw [← Finset.sum_apply, grantsU,Finset.sum_apply, show R₀ᶜ=univ.filter (fun i:Site D₀=>i∉R₀) from by ext; simp,sum_filter]; refine sum_congr rfl fun i _=>by split <;> simp_all
 rw [hF,hF]; have ht(i:Site D₀)(hg:i∈R₀ᶜ): V0 i=τ A' i -τ P₀ i+ I' (α+b) i- I' α i:=by
    have hp:= (mem_compl.mp hg); obtain ⟨hy,hz⟩:=hv i hp
    let ht:= studio G F Q x d u q l (rough S 0) A' β t h i (fun t=> hp (farther (Nat.mul_le_mul_right _ hx) t)) ⟨hz.found⟩ hy rfl
    have hx:Facet.plain F x q d u l Q t k₀ i 1=τ P₀ i:=by
       have he:= pines_o F x u l Q t h.funds h.ready (h.tall (S.park,S.k)) h.pay (h.ears _) h.sizes
       rw [song _ _ _ _ _ _ _ t h.funds h.ready (h.tall _) h.pay (h.ears _) h.sizes h.fine he]; unfold turf τ fJ; refine sum_congr rfl fun k _=>?_ ; have hh:hornY F q x d l k₀ 1=P₀.val:= by rw [p0]; exact Prod.ext (stillW F x k₀ q d l 0 h.funds).2 rfl
       unfold Facet.test; simp_rw [hh,pear_even G t P₀.property]
    unfold V0 snowG; rw [kappaY _ _ _ _ _ _ _ J v w]; change Facet.plain F x q d u l Q t k₀ i S.V -_+ (I' b i-I' 0 i)=_; rw [show Facet.plain F x q d u l Q t k₀ i S.V=τ A' i from ht,hx]; have hc:I' (α+b) i= I' α i+(I' b i-I' 0 i):=coinI _ _ _ _ _ _ _ _ _ _ _ _; rw [hc]; abel
 let U:= mintB G Q x; have hh(D:Rent0 G e):Φ D.val=(∑ i∈R₀,τ D i)+(∑ i∈R₀ᶜ,τ D i)+U D:=by rw [sum_add_sum_compl]; exact fond _ _ _ _ _ (h.pay)
 rw [←p0,hh,hh]; unfold scenic posy rockS pearQ; change - (∑ i∈R₀ᶜ,I' (α+b) i)-_= _ -(∑ i∈R₀ᶜ,V0 i)-_
 rw [Finset.sum_congr (s₁:=R₀ᶜ) (f:=V0) rfl ht]; unfold τ I' -- tune; U too
 simp only [sum_sub_distrib,sum_add_distrib]; unfold U; abel
end
end YM.CF.Corne
#print axioms YM.CF.Corne.visaS
