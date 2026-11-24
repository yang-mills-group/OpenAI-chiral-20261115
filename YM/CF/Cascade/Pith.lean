import YM.CF.Cascade.Patch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Pec
local notation "mμ"=> Cascade.pulse
local notation "ωX"=> Aroma.port
abbrev pee : PlaqAxes:= ⟨(0,1),by decide⟩
def tyM (n:Side): Site (More n):= step 0
def brok(n:Side):= cell (tyM n) (step 0)-1
def springY(n:Side)(i:Body 2 (More n)):= brok n*rotations (More n) _ i (tyM n,plaquette pee)
lemma boltC(z: ℂ→L[ℝ]ℝ)(p:3≤(More n).val): d 1 (More n) *ᵥ pill n (groan z (hike (ωX n)))= fun i=> z (springY n i):=by
 ext1 ⟨i,v⟩; obtain ⟨v,rfl⟩:= plaqEquiv.surjective v
 rw [← mon0 p]; let Z:=tyM n; let U:= groan z (hike (n:=More n) (mon Z)); change (d _ _ *ᵥ pill n U) (i,plaquette v)=_ ; rw [d_plaquettes]; have hq(a:Axis):coord a=coord 1 ↔ a=1:= axisEquiv.apply_eq_iff_eq
 have he(a:Axis): a≠0→ cell Z (step a)=1:=by intro h; rw [cell_step,show mon Z=ωX n from mon0 p]; simp [Aroma.port,Ember.spark,h]
 rcases v with ⟨⟨a,b⟩,h⟩; change a<b at h
 unfold pill; by_cases hp : a=0 ∧ b=1
 · obtain ⟨rfl,rfl⟩:=hp; change (if coord (1: Axis)=coord 1 then U (i+step 0) else 0) - (if coord 1=coord 1 then U i else 0)-( (if coord 0=coord 1 then U (i+step 1) else 0)-(if coord 0=coord 1 then U i else 0))=z (brok n* (if plaquette pee=plaquette pee then cell Z i else 0)); simp only [hq,ite_true,show (0:Axis) ≠1 from by decide,ite_false,sub_zero]; change z (cell Z _)-z (cell Z _)= z _; rw [←map_sub,cell_add]; unfold brok Z; congr 1; ring
 have hz:springY n (i,plaquette ⟨(a,b),h⟩)=0:=by simp [springY,rotations,plaq_iff,hp]
 rw [show springY n (i,plaqEquiv ⟨(a,b),h⟩)=0 from hz,map_zero]; by_cases v:b=1
 · subst b; exact absurd ⟨(show ∀ i:Axis,i<1→ i=0 by decide) a h,rfl⟩ hp
 by_cases he':a=1; · subst a; simp only [hq, v,ite_false, ite_true,sub_self]; change 0-(z (cell Z _)- z (cell Z i))=0; rw [cell_add,he b ((show ∀ i:Axis, 1< i→ i≠0 by decide) _ h),mul_one]; abel
 simp [hq,v,he']
def date(n:Side):ℝ:=Fintype.card (Site (More n))
@[simp] lemma date_pos(n:Side):0<date n:=by unfold date; positivity
lemma ebb (H:Bed)(n:Side)(p:H.metric.safe)(x:Orig n): let v:= (x,plaquette pee); (approached (H.metric.acts (More n)) *ᵥ springY n) v=springY n v * H.metric.read (mon (tyM n)) (plaquette pee) (plaquette pee):=by
 intro v; let f:= H.metric; let P:=approached (f.acts (More n)); let i:=tyM n; let D:= More n; let X:=rotations D (TypeFace 2); let j:=plaquette pee; have he := congrArg (fun F=> (F:Matrix _ _ ℂ) v (i,j)) (circulant D f p); have hx(i'): springY n i'=brok n * X i' (i,j):=rfl; rw [hx]; rw [show (approached (H.metric.acts D) *ᵥ (springY n)) v= brok n*((P*X) v (i,j)) from ?_,show P*X=X*fiber (fun i:Site D=>f.read (mon i)) from circulant D f p,rot_fiber]; swap; · unfold Matrix.mulVec dotProduct; rw [Matrix.mul_apply, mul_sum]; apply sum_congr rfl; intro i _; rw [hx]; unfold P f; ring
 unfold X rotations; simp only [v,Matrix.of_apply, j,ite_true,←mul_assoc]; rfl -- tune
lemma account(P:Bed)(u:CoreX)(x:Air n)(w:‖u‖=1):Bid.gaugeFiscal P (pour n u x) (pour n u x)=let v:= d 1 (More n) *ᵥ pill n x; dotProduct v (P.metric.acts (More n) *ᵥ v):=by
 dsimp only; rw [Channel.fiscal_flux]; simp_rw [quadR, Matrix.mulVec_smul, dotProduct_smul,smul_dotProduct, smul_eq_mul,← mul_assoc, ← sum_mul]; rw [show ∑ i:group.ColorIndex, u i*u i=1 from ?_,one_mul]
 have he:= Work.F03.inner_color (G:=group) u u; rw [real_inner_self_eq_norm_sq,w,one_pow] at he; exact he.symm
lemma act_z {ι:Type}[Fintype ι](P:Matrix ι ι ℝ)(x:ι→ℂ)(i:ι)(V:ℂ→L[ℝ]ℝ): V ((approached P *ᵥ x) i)=(P *ᵥ fun k=>V (x k)) i:=by unfold Matrix.mulVec dotProduct; rw [map_sum]; apply sum_congr rfl; intro j _; exact map_smul V (P i j) (x j)
lemma price_b (R:RG.PathData SU.group)(q:RG.Clip)(P:Bed){σ η A B C:ℝ}(h:R.Bounds q σ A B)(p:Floor P q (More n) η C)(he:P.metric.safe)(g:Attached P R)(u:Bid.Sworn P (More n) SU.group) (v:CoreX)(hv:‖v‖=1)(t:3≤(More n).val): (syl (copper n v (secondM q R)) (hike (ωX n)) (hike (ωX n))).re= date n * (‖brok n‖^2 * (P.metric.read (ωX n) (plaquette pee) (plaquette pee)).re):=by
 let s:= secondM (n:=n) q R; let x:= hike (n:=More n) (ωX n)
 have hx(z : ℂ→L[ℝ]ℝ): copper n v s (groan z x) (groan z x)= let Q := (fun i:Body 2 (More n)=>z (springY n i)); dotProduct Q (P.metric.acts (More n) *ᵥ Q):=by
    dsimp only; let a:=groan z x; have ht:= asideF ((sane h).of_le (m:=(↑(2:ℕ))) le_top) _ (toned (d:=0) h p g u); rw [copperP _ _ ((sane h).of_le le_top),show trim 2 _ _=(↑(Bid.gaugeFiscal P (pour n v a) (pour n v a)/2):ℂ) from (ht.2 _).symm, Complex.ofReal_re]; rw [show 2*(Bid.gaugeFiscal P (pour n v a) (pour n v a)/2)= Bid.gaugeFiscal P (pour n v a) (pour n v a) by ring]
    rw [account P v a hv]; unfold a x; rw [boltC z t]
 change copper n v s (grove n _) (grove n _) + copper n v s (waveL n _) (waveL n _)= _; rw [show grove n (hike (ωX n))=_ from (rfl : _=groan (n:=n) Complex.reCLM x), show waveL n (hike (ωX n))=_ from (rfl : _=groan (n:=n) Complex.imCLM x),hx Complex.reCLM,hx Complex.imCLM]; dsimp only
 let L:=P.metric.acts (More n); let g:= springY n; let W:= (P.metric.read (ωX n) (plaquette pee) (plaquette pee)); let T:=tyM n
 change (∑ i:Body 2 (More n),(g i).re*(L *ᵥ (Complex.reCLM∘ g)) i)+(∑ i:Body 2 (More n),(g i).im*(L *ᵥ (Complex.imCLM∘ g)) i)=date n*_
 rw [← sum_add_distrib]; unfold Body; rw [Fintype.sum_prod_type, show date n*(‖brok n‖^2*W.re)=∑ _ : Orig n,(‖brok n‖^2 * W.re) by rw [sum_const,card_univ,nsmul_eq_mul]; rfl]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single (plaquette pee)]; swap; intro y _ h; rw [show g (i,y)=0 from ?_]; simp; simp [g,springY,rotations,h]; swap; simp
 let z:= (i,plaquette pee); let v:= g z
 have he : (approached L *ᵥ g) z= v*W:=by have hz:= ebb P n he i; dsimp only at hz; rw [show mon (tyM n)=ωX n from mon0 t] at hz; exact hz
 have ht(j:ℂ→L[ℝ]ℝ):(L *ᵥ (j∘ g)) z=j (v*W):=by rw [← he]; exact (act_z L g z j).symm
 rw [show (L *ᵥ _) (i,plaquette pee)=_ from ht Complex.reCLM, show (L *ᵥ _) (i,plaquette pee)=_ from ht Complex.imCLM]; have hp:‖v‖=‖brok n‖:=by unfold v g z springY; simp only [rotations, Matrix.of_apply, ite_true]; rw [norm_mul,show ‖cell T i‖=1 from mode_real (mon T) _ (real_frequency T),mul_one] -- T tune
 change v.re*(v*W).re+ v.im*(v*W).im=_; rw [Complex.mul_re,Complex.mul_im,←hp, Complex.sq_norm]; unfold Complex.normSq; simp; ring
end YM.CF.Cascade
