import YM.SU5.Gleam.Lacuna
import YM.SU5.Gleam.Parlor
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ledger
/-! # Affine FI row cost measured with the very same derivative operators -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X Y:fieldDir G n 1} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L:Floor H q n δ w)
-- linearize by coloring rows. WithLp applied only once
abbrev Altar (G:Gauge) (n:Side):= EuclideanSpace ℝ ((Cell n) × Bool × G.ColorIndex)
def tiler (B:Z.Bounds q η C S)(P:Attached H Z) : fieldDir G n 1 →ₗ[ℝ] Altar G n where
 toFun X:=WithLp.toLp 2 fun b=> if b.2.1 then (ellLine Z b.1 X) b.2.2 else Real.sqrt q.direct * faceCurl b.1 X b.2.2
 map_add' X Y:=by
    have h(k:Body 2 n)(i:G.ColorIndex) : (dColor G n 1 (X+Y) k) i=(dColor G n 1 X k) i+(dColor G n 1 Y k) i:=by unfold dColor; change (d 1 n*ᵥ (parts G 1 X i+parts G 1 Y i)) k=_; rw [Matrix.mulVec_add]; rfl
    ext ⟨b,k,i⟩; cases k
    · exact (congrArg (Real.sqrt q.direct * ·) (h (b.1,plaquette b.2) i)).trans (mul_add ..)
    change ellLine Z b (X+Y) i= ellLine Z b X i+ _; rw [ellLine_mulVec H B P,ellLine_mulVec H B P]; change (H.roots.acts n *ᵥ _) _= _ + ellLine Z b Y i; rw [ellLine_mulVec H B P, show parts G 1 (X+Y) i=parts G 1 X i + parts G 1 Y i from rfl,Matrix.mulVec_add,Matrix.mulVec_add]; rfl
 map_smul' a X:=by
    have h(k:Body 2 n)(i:G.ColorIndex) : dColor G n 1 (a • X) k i= a * dColor G n 1 X k i:=by unfold dColor; change (d 1 n *ᵥ (a • parts G 1 X i)) k=a*_; rw [Matrix.mulVec_smul]; rfl
    ext ⟨b,k,i⟩; cases k
    · change Real.sqrt q.direct * faceCurl b (a•X) i=a*(Real.sqrt q.direct*faceCurl b X i); rw [faceCurl,h]; unfold faceCurl; ring
    change ellLine Z b (a•X) i=a*ellLine Z b X i; rw [ellLine_mulVec H B P,ellLine_mulVec H B P, show parts G 1 (a•X) i=a•parts G 1 X i from rfl,Matrix.mulVec_smul,Matrix.mulVec_smul]; rfl

def stock (T : Forest r)(b:Finset T.Free) (x:LogArray G b) : fieldDir G n 1:=fun v=> ∑ j:b,(seatsF T b v j)• x j
private lemma stockV (T : Forest r)(F:Finset T.Free)(x : Prices G F)(i:G.ColorIndex): let f(j:↥F):=x (j,i); parts G 1 (stock T F (tape x)) i = seatsF T F *ᵥ f:= by
 intro f; funext j; unfold parts stock; change (∑ k:↥F, seatsF T F j k • tape x k) i = _
 change (EuclideanSpace.proj i) (∑ k:↥F, seatsF T F j k • tape x k)=_; rw [map_sum]; rfl -- instance search
abbrev stockLine (T:Forest r)(F:Finset T.Free): LogArray G F →ₗ[ℝ] fieldDir G n 1:={
 toFun:= stock T F
 map_add':=fun x y=> by ext j i; unfold stock; change (∑ k:↥F,seatsF T F j k • (x k+y k)) i=_; simp_rw [smul_add, Finset.sum_add_distrib]; rfl
 map_smul':=fun a x=> by ext j i; unfold stock; change (∑ k:↥F,seatsF T F j k • a • x k) i=_; simp_rw [smul_comm (seatsF T F j _) a,← Finset.smul_sum]; rfl }
-- masks offset only
abbrev accession (B:Z.Bounds q η C S)(P:Attached H Z) (r:Ratio c n)(A:Support c)(m:ℕ)(V:fieldDir G n 1): Altar G n:= WithLp.toLp 2 fun i=> if insideB r A m i.1 then (tiler B P V) i else 0
include B P
lemma tiler_color (X:fieldDir G n 1) : ∀ (b:Cell n), (∑ i:Bool×G.ColorIndex, (tiler B P X (b,i))^2)= 2*research Z q b X:=by
 intro b; let f(i:Bool)(j:G.ColorIndex):=(tiler B P X (b,i,j))^2
 change ∑ i:Bool×G.ColorIndex, f i.1 i.2=_
 rw [Fintype.sum_prod_type,Fintype.sum_bool] -- true then false?
 let y:=faceCurl b X; have he : ∑ j,f false j=q.direct * ‖y‖^2:=by
    simp_rw [show ∀ j : G.ColorIndex, f false j=q.direct * (y j)^2 from fun j=> by unfold f; change (Real.sqrt q.direct * y j)^2=_; rw [mul_pow,Real.sq_sqrt q.quadratic_pos.le]]
    rw [← mul_sum,EuclideanSpace.real_norm_sq_eq]
 let w':=ellLine Z b X; have hp:∑ j,f true j= ‖w'‖^2:= by rw [EuclideanSpace.real_norm_sq_eq]; rfl
 rw [he,hp]; unfold research; unfold y w'; ring
lemma tiler_occupy (X V:fieldDir G n 1)(A:Support c) : ∑ b:Cell n,rent Z q r A m b X V= ‖tiler B P X + accession B P r A m V‖^2/2:=by
 let Φ:= tiler (n:=n) B P; let W:= accession B P r A m V
 conv_rhs=> rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type, Finset.sum_div] -- orientation sum_div
 apply Finset.sum_congr rfl; intro i _; unfold rent; split
 next h=>
    have he(j:Bool × G.ColorIndex): (Φ X+W) (i,j)= Φ (X+V) (i,j):=by rw [map_add]; simp [W, accession, h,Φ]
    change research Z q i _=_; change _=(∑ j:Bool × G.ColorIndex, ((Φ X+W) (i,j))^2)/2; simp_rw [he]; rw [show ∑ j:Bool× G.ColorIndex,_=_ from tiler_color B P (X+V) i]; ring
 next h=>
    have he(j:Bool×G.ColorIndex): (Φ X+W) (i,j)= Φ X (i,j):=by simp [W,h,accession]
    change _=(∑ j:Bool × G.ColorIndex, ((Φ X+W) (i,j))^2)/2; simp_rw [he]; rw [show ∑ j:Bool × G.ColorIndex,_=_ from tiler_color B P X i]; ring
-- square under RHS tape
abbrev cellM (T:Forest r)(F:Finset T.Free) (H:Bed):= coinVec T F (Precision.K (H.metric.acts n))
abbrev prism (T:Forest r) (F:Finset T.Free)(H:Bed)(G:Gauge) := cellM T F H ⊗ₖ (1:Sheet G.ColorIndex)
include L
lemma Tape_price (x:Prices G F): ‖tiler B P (stock T F (tape x))‖^2=qpay (prism T F H G) x:=by
 let X:= stock T F (tape x); let D:= cellM T F H; let Ψ(i:G.ColorIndex)(j:↥F):= x (j,i); let A:=H.metric.acts n
 let T':= tiler (n:=n) B P; have he: ‖T' X‖^2= Bid.gaugeFiscal H X X:=by
   rw [metric_pair H B P X X L,EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; dsimp only; rw [show ∑ j:Bool×G.ColorIndex, (T' X (i,j))^2=_ from tiler_color B P X i,research]; simp_rw [real_inner_self_eq_norm_sq]; ring
 change ‖T' X‖^2=_; rw [he]; unfold Bid.gaugeFiscal
 have hp(i:G.ColorIndex):dotProduct (parts G 1 X i) ((Precision.K A)*ᵥ parts G 1 X i)=qpay D (Ψ i):= by rw [show parts G 1 X i=seatsF T F*ᵥ Ψ i from stockV ..]; exact (qgain (Precision.K A) _).symm
 have hv(i:G.ColorIndex)(j:↥F) : (prism T F H G*ᵥ x) (j,i)=(D *ᵥ Ψ i) j:=by
   unfold Matrix.mulVec dotProduct prism; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro l _; dsimp only; rw [sum_eq_single i] -- tune
   · rw [kroneckerMap_apply]; simp; rfl
   · intro k _ w; change D j l*(1:Sheet G.ColorIndex) i k * _=_; rw [one_apply_ne w.symm]; ring
   simp
 change (∑ i, dotProduct (parts G 1 X i) ((Precision.K A)*ᵥ parts G 1 X i))=_; simp_rw [hp]; unfold qpay dotProduct; rw [Fintype.sum_prod_type,sum_comm]; simp_rw [hv]; rfl
omit L B P in
lemma coupling_inter (x:ℝ)(p:0<x): x * coupling x ^ 2 = 1:=by unfold coupling; rw [inv_pow,Real.sq_sqrt p.le,mul_inv_cancel₀ p.ne']
def yieldY (Z:PathData G)(q:Clip)(T:Forest r)(F:Finset T.Free)(A:Support c)(m:ℕ)(Y:fieldDir G n 1)(β:ℝ)(x:LogArray G F):= Real.exp (-β*∑ b:Cell n,rent Z q r A m b (stock T F x) Y)
lemma roundMeasure (Y:fieldDir G n 1)(h:(cellM T F H).PosDef)(p:0<β) : let f:=yieldY Z q T F A m Y β; let K:=chartCost (prism T F H G)⁻¹ (coupling β); Integrable f volume ∧ (∫ x,f x) ≤ K:=by
 let Ψ:= (prism T F H G); let σ:= coupling β
 let Φ:= tiler (n:=n) B P; let D:= accession B P r A m Y; let O:= LinearMap.comp Φ (stockLine T F); let W:= O.comp (colors (G:=G) (ι:=↥F)).toLinearMap
 have hf: Ψ.PosDef:= h.kronecker PosDef.one; let X:= LinearMap.range W; let g:= coupling_pos p
 obtain ⟨a,ha,b,hb,he⟩:= X.exists_add_mem_mem_orthogonal D
 obtain ⟨x,hx⟩:= ha; let c':= - x; have hE: D=a+b:=by first| exact he|exact he.symm
 intro f K
 obtain ⟨hq,ht⟩:= at_price Ψ⁻¹ hf.inv g c' f; let V:=cloud Ψ⁻¹
 let L':=Real.exp (-β* (‖b‖^2/2))
 let F'(x:Prices G F):=Real.exp (force Ψ⁻¹ x/2) • f (displaced c' σ x)
 have he' : F'=fun _=>L':=by
    funext y; unfold F' f yieldY L'; rw [tiler_occupy B P]; let t:=displaced c' σ y
    have h : Φ (stock T F t)+D= σ • W y+b:=by
       rw [hE,←hx]; change W (-x+σ • y)+(W x+b)=_; rw [map_add,map_neg,map_smul]; abel
    rw [show (tiler B P) _ + _=_ from h,norm_add_sq_real (σ • W y) b,show inner ℝ (σ • W y) b=0 from ?_,mul_zero,add_zero]
    · rw [norm_smul,Real.norm_of_nonneg g.le,mul_pow]; let Y:=qpay Ψ y; have hv : ‖W y‖^2=Y:=Tape_price B P L y
      rw [hv,show force Ψ⁻¹ y=Y from (?_),smul_eq_mul, ← Real.exp_add]; swap; · unfold force; rw [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hf.isUnit)]; rfl
      have hw:β*σ^2=1:=coupling_inter _ p; congr 1; linarith only [show β*σ^2 * Y =Y by rw [hw,one_mul]]
    exact (Submodule.mem_orthogonal _ b).1 hb _ (X.smul_mem _ ⟨y,rfl⟩)
 let J:=integrable_const (μ:=V) L'; rw [← he'] at J; have hu: (∫ x,F' x ∂V)≤1:=by rw [he',integral_const]; simp only [probReal_univ, one_smul]; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.le) (by positivity)
 refine ⟨hq.2 J,ht.trans_le ?_⟩; change K • _ ≤ K; rw [smul_eq_mul]; exact mul_le_of_le_one_right (chartCost_pos _ hf.inv g).le hu

omit L B P in
lemma prism_spec (J:ChartRatio G) (p:LocalRatio J)(g:0<β)(h:(cellM T F H).PosDef) : Real.log (J.scale ^ F.card * chartCost (prism T F H G)⁻¹ (coupling β)) = F.card * Real.log (spare J β) - (Fintype.card G.ColorIndex:ℝ) / 2 * Real.log (cellM T F H).det:=by
 let τ:=prism T F H G; let α:=Fintype.card G.ColorIndex; let X:=cellM T F H; let m:=Fintype.card (↥F); let σ:= coupling β
 have hz : τ.PosDef:= h.kronecker PosDef.one; have he := coupling_pos g; have hw:Real.log (chartCost τ⁻¹ σ)= Real.log (Real.sqrt (2 * Real.pi * σ^2)) * (m*α)+ Real.log (τ⁻¹).det/2:=by -- m*α Nat cast or ℝ?
    unfold chartCost; have h:0<2*Real.pi*σ^2:=by unfold σ; positivity
    rw [Real.log_mul (pow_pos (Real.sqrt_pos_of_pos h) _).ne' (Real.sqrt_pos_of_pos hz.inv.det_pos).ne',Real.log_pow,Fintype.card_prod, Real.log_sqrt hz.inv.det_pos.le,Nat.cast_mul]; unfold α m; ring
 rw [Real.log_mul (pow_ne_zero _ p.scale.ne') (chartCost_pos τ⁻¹ hz.inv he).ne', Real.log_pow, hw]; let F':=Real.sqrt (2 * Real.pi * σ^2); have hF:0<F':=by unfold F' σ; positivity
 rw [show spare J β= F'^α* J.scale from rfl,Real.log_mul (pow_pos hF _).ne' p.scale.ne',Real.log_pow]; rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv]; unfold τ prism; rw [det_kronecker, det_one,one_pow,mul_one,Real.log_pow]; unfold F' α m; rw [Fintype.card_coe]; ring -- τ det expression hw maybe
end YM.Gleam
#print axioms YM.Gleam.roundMeasure
#print axioms YM.Gleam.prism_spec
