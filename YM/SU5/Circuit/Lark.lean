import YM.SU5.Circuit.Regale
import YM.SU5.Regis.Easel
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Head.Brecht
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit
open scoped Matrix Topology BigOperators ComplexConjugate NNReal ENNReal InnerProductSpace
variable {q: Clip}{n: Side}{M: Bed}{G:Gauge}{Z:PathData G}{η C v σ θ w a:ℝ}
variable (B: Z.Bounds q θ w a)(P:Attached M Z)(L:Floor M q n η C)(H:M.covered σ C)(e:0<σ)
variable (i j:G.ColorIndex)(X Y:Body 2 n)
local notation "r"=> stamen B P n
local notation "t"=>tiler B P
abbrev orbe : Body 2 n≃Face (Per n):= Equiv.prodCongr (Equiv.refl _) plaqEquiv.symm
abbrev beamZ: r →L[ℝ] G.Color := (Etch.river (G:=G) q (orbe X)).toContinuousLinearMap.comp (stamen B P n).subtypeL
abbrev zion : StrongDual ℝ r:= (EuclideanSpace.proj i).comp (beamZ B P X)
def trill : r:=(InnerProductSpace.toDual ℝ (r)).symm (zion B P i X)
lemma joy (x:r): inner ℝ (trill B P i X) x=beamZ B P X x i:=by
 let g:= InnerProductSpace.toDual ℝ (r); change g (g.symm _) _=_; rw [LinearIsometryEquiv.apply_symm_apply]; rfl
lemma inspire (b: Lattice.PlaqAxes)(x:Site n)(h:r): beamZ B P (x,plaquette b) h= Etch.river q (x,b) h.val:=by change Etch.river q (x,plaqEquiv.symm (plaquette b)) h.val=_; rw [← plaq_map,Equiv.symm_apply_apply]
lemma praises(A: fieldDir G n 1): inner ℝ (trill B P i X) ((t).rangeRestrict A)=(d 1 n*ᵥ parts G 1 A i) X:=by
 obtain ⟨x,v⟩:=X; obtain ⟨b,rfl⟩:= plaqEquiv.surjective v; rw [joy,plaq_map,inspire]; exact congrArg (fun x:G.Color=>x i) (Etch.river_now _ B P (x,b) A)
abbrev starlet (B:Z.Bounds q θ w a)(P:Attached M Z)(n:Side)(x:fieldDir G n 1) : stamen B P n := (tiler B P).rangeRestrict x
def zoneP: Matrix (Body 2 n) (Body 2 n) ℝ:= Matrix.of fun X Y=> inner ℝ (trill B P i X) (trill B P j Y)
lemma song (x:r): ∃ y, (t).rangeRestrict y=x:=by obtain ⟨y,h⟩:= x.property; exact ⟨y, Subtype.ext h⟩
lemma zoneW : ∃ T:Matrix (Body 1 n) (Body 2 n) ℝ,zoneP (n:=n) B P i j=d 1 n*T:=by
 choose X e using fun x:Body 2 n=>song B P (trill B P j x); refine ⟨Matrix.of fun w x=> parts G 1 (X x) i w,?_⟩; ext a b; unfold zoneP; rw [of_apply,← e,praises]; rfl
include L in
lemma marksOne (x y: fieldDir G n 1): inner ℝ ((t).rangeRestrict x) ((t).rangeRestrict y)= Bid.gaugeFiscal M x y:=by
 let V(x: fieldDir G n 1):=‖t x‖^2; let F(x y:fieldDir G n 1):=Bid.gaugeFiscal M x y; let B'(x):=F x x; have v(x):V x=B' x:= face_map B P L x
 have hx(x y: fieldDir G n 1): F x y=F y x:=by unfold F; rw [metric_pair M B P _ _ L, metric_pair M B P _ _ L]; apply sum_congr rfl; intro i _; congr 1 <;> first| rw [real_inner_comm _ (faceCurl .. y)]| rw [real_inner_comm] -- tune
 have he : V (x+y)= V x+2*inner ℝ (t x) (t y)+V y:=by unfold V; rw [map_add,norm_add_sq_real]
 have ht:B' (x+y)=B' x+2*F x y+B' y:=by
    unfold B'; have hv (x y z:fieldDir G n 1): F (x+y) z=F x z + F y z:= gaugeFiscal_add .. ; rw [hv,hx x (x+y), hx y (x+y),hv,hv,hx x y]; ring
 change inner ℝ (t x) (t y)=F x y; linarith only [ht,he,v x,v y,v (x+y)]
-- matrix equation using single color link
abbrev fink(G: Gauge)(i:G.ColorIndex)(x:Body 1 n→ℝ):fieldDir G n 1:= fun a=> EuclideanSpace.single i (x a)
def sch (i j:G.ColorIndex):ℝ:= if i=j then 1 else 0
include L in
lemma sideSong : (zoneP B P i j).transpose*M.metric.acts n*d 1 n=(sch (G:=G) i j)•(d 1 n):=by
 let A':=M.metric.acts n; let E:= Precision.K A'; let V(y:Body 2 n):= trill B P j y
 apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; ext y
 let w:=fink G i x; let b(p:G.ColorIndex):= parts G 1 w p; let S:= d 1 n
 have hb: b i=x:=by ext k; simp [b,w,parts,fink]
 have hv(c:G.ColorIndex)(e:c ≠ i): b c=0:=by ext k; simp [b,w,parts,fink,e,Ne.symm e]
 obtain ⟨w',p⟩ :∃ a:fieldDir G n 1,(t).rangeRestrict a=V y := song B P _
 let W:= (S*ᵥ parts G 1 w' i); have ht(k:Body 2 n): (zoneP B P i j) k y=W k:=by change inner ℝ (trill B P i k) (V y)=_; rw [←p,praises]
 have hh : Bid.gaugeFiscal M w' w= dotProduct W ((A'*S)*ᵥ x):=by
    unfold Bid.gaugeFiscal; rw [sum_eq_single i]; swap; · intro c _ e; rw [show parts G 1 w c=0 from hv c e]; simp
    swap; · simp
    rw [show parts G 1 w i=_ from hb,Precision.K]; unfold W; rw [Matrix.mul_assoc, ←mulVec_mulVec x, dotProduct_mulVec (parts G 1 w' i), Matrix.vecMul_transpose]
 let H:= sch (G:=G) i j; change ((_ * _ * _) *ᵥ x) y=((H•S)*ᵥx) y
 rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec]
 calc _= W ⬝ᵥ ((A' * S)*ᵥ x):=by simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,ht]; rfl
      _= inner ℝ (V y) ((t).rangeRestrict w):=by rw [←p,marksOne B P L,hh]
      _=_:=by unfold V; rw [praises, Matrix.smul_mulVec,Pi.smul_apply]; by_cases h:j=i
              · subst j; rw [show parts G 1 w i=_ from hb]; simp [sch,H,S] -- hb match
              rw [show parts G 1 w j=0 from hv j h]; simp [sch,H,h,Ne.symm h]
lemma appraisal {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E](x y:E): (∫ z, inner ℝ x z * inner ℝ y z ∂ stdGaussian E)= inner ℝ x y:=by
 have he:= covarianceBilin_apply (μ:=stdGaussian E) IsGaussian.memLp_two_id x y; rw [covarianceBilin_stdGaussian] at he; simp only [id, integral_id_stdGaussian,sub_zero] at he; exact he.symm
-- exact two-point statement
include L H e in
theorem chimes (v:Even n.val): (↑(∫ s:stamen B P n, (beamZ B P X s i)*(beamZ B P Y s j)∂stdGaussian (stamen B P n)):ℂ)= (sch (G:=G) i j:ℂ)*rimble n M X Y:=by
 simp_rw [← joy, appraisal]; obtain ⟨T,h⟩:=zoneW (n:=n) B P i j; exact congr_fun (congr_fun (coin_down L H e v _ _ _ h (sideSong B P L i j)) X) Y
end YM.Regis.Head.Brecht
#print axioms YM.Regis.Head.Brecht.chimes
