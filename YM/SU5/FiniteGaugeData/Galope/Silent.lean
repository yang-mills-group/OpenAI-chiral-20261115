import YM.SU5.FiniteGaugeData.Galope.Nib
import YM.SU5.FiniteGaugeData.Galope.Mime
import YM.Next.FLUCTUATIONS.Linear
import YM.Work.E04
/-! # Loewner lower bound for calibrated gauge purchase on interior, and price vs the WP15 chassis.
 Actual angular coordinates (coframe of Gauge). Measure cost is Haar not these linearized arrays; priced elsewhere. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle
open Pressure Precision Exterior Laurent Bloch Next.Fluctuations Work.E03
open Drachma Drachma.Toffee Avenue Wrist Press Poeme Work.F03
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {F:Clip}{n:Side}{G:Gauge} {s:Stage}{R:PathData G}{P:Bed}{M k w v:ℕ}{A:Finset (Cell n)}{Z:Finset (Site n)}{o:Site n}{C r x Λ α τ u a h:ℝ}
namespace Haute
local notation "φ₀" => s.clip
variable {I:Finset (Bond n)}
def bid(Y:Finset (Bond n))(x:LogField G n): Prop:= ∀ i:Bond n, i∉ Y→ x (markZ n i)=0
private lemma empty_curl (x:LogField G n)(i j:Cell n) (v:separation i.1 j.1≤w+3)(hx:bid (buy Z k) x)(h: i∉ billsC k w Z): Work.F03.faceCurl j x=0:=by
 have he(y:Bond n)(p:separation j.1 y.1≤1): x (markZ n y)=0:= by
    apply hx; intro t; apply h; obtain ⟨o,q,r⟩:= mem_biUnion.mp t; have hm: separation y.1 i.1≤ w+4:=by rw [separation_comm]; exact (separation_triangle ..).trans ((add_le_add v p).trans le_rfl)
    apply inBooks.mpr; refine ⟨o,q,?_⟩; rw [roomCard,add_assoc]; exact Avenue.extend o _ _ hm (mem_filter.mp (mem_product.mp r).1).1 -- tune $k+(w+4) not defeq?$ yes nat+4.
 ext i; change (d 1 n*ᵥ parts G 1 x i) (j.1,plaquette j.2)=0; rw [d_plaquettes]; let a:=j.2.val.1; let b:=j.2.val.2; have hv(y:Bond n)(p:separation j.1 y.1 ≤ 1): parts G 1 x i (y.1,coord y.2)=0:=by unfold parts; rw [show (y.1,coord y.2)=markZ n y from rfl,he y p]; rfl
 rw [hv (j.1+step a,b) (sep_step j.1 _),hv (j.1,b) (by dsimp; rw [separation_self]; omega),hv (j.1+step b,a) (sep_step j.1 _),hv (j.1,a) (by dsimp; rw [separation_self]; omega)]; ring -- tune matching rw
lemma tail_visit (x:LogField G n)(i:Cell n)(hx:bid (buy Z k) x)(h: i∉ billsC k w Z)(y:RG.Slot)(e:y.length ≤ w): faceCurl (slotFace y i.1) x=0:= empty_curl x i _ ((Work.E04.slot_separation y i.1).trans (e.trans (by omega))) hx h -- tune
abbrev primeShare(w:ℕ)(s:Stage):= (Fintype.card PlaqAxes:ℝ)*(s.paths*tar s.width w)^2/s.clip.direct
lemma bookShare(x:LogField G n)(hx:bid (buy Z k) x)(W:R.Bounds φ₀ s.width s.paths Λ):
 (1-primeShare w s)* accepts s R univ x ≤ accepts s R (billsC k w Z) x:=by
 let Y(j:Cell n):=faceCurl j x; let B:=billsC k w Z; let V(q:Cell n):= if q∉B then ellLine R q x else 0; let D:=s.paths*tar s.width w
 have he(i:PlaqAxes): cash (fun j:Site n=> V (j,i))≤ D*cash Y:=by
    let X(z:ℕ)(j: Site n): G.Color:= if (j,i)∉B then (R.row i z).1 • Y (slotFace (R.row i z).2 j) else 0
    have hu(j:Site n): V (j,i)=∑' z:ℕ,X z j:=by
       by_cases ht:(j,i)∉B; · simp only [V,X,if_pos ht]; rfl
       simp only [V,X,if_neg ht,tsum_zero]
    simp_rw [hu]; refine (earned Y X i w W ?_).2; intro j l; unfold X; split; next ht=>
       split; next p=> rw [norm_smul,Real.norm_eq_abs]
       next p=> rw [show Y _= _ from tail_visit (Z:=Z) (k:=k) (w:=w) x (l,i) hx ht _ (Nat.le_of_not_gt p), smul_zero,norm_zero]
    next ht=> split<;> rw [norm_zero] <;> positivity
 let δ:= primeShare w s
 have hδ:0≤δ:=by unfold δ primeShare; have hp:=s.clip.quadratic_pos; positivity
 have H: cash V ^2 ≤ δ*(s.clip.direct * cash Y^2):=by
    rw [pay,Fintype.sum_prod_type,sum_comm]; calc
      _ ≤ (Fintype.card PlaqAxes:ℝ)*(D*cash Y)^2:= by apply (sum_le_sum (g:=fun i=>(D*cash Y)^2) (fun (i:PlaqAxes) _=> ?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul]); rw [←pay]; exact pow_le_pow_left₀ (pay_pos _) (he i) 2
      _ = _:=by have hp:=s.clip.quadratic_pos; unfold δ D primeShare; field_simp
 let coreP(i:Cell n):=∑ t:Bool, ‖xLin φ₀ R x (i,t)‖^2; let d:=s.clip.direct; have hd(i:Cell n): coreP i=d* ‖Y i‖^2+ ‖ellLine R i x‖^2:=by unfold coreP; rw [Fintype.sum_bool]; simp only [xLin,Bool.false_eq_true,↓reduceIte,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt s.clip.quadratic_pos.le,add_comm]; rfl
 have hm : d*cash Y^2 ≤ ∑ i,coreP i:=by
    rw [pay,mul_sum]; exact sum_le_sum fun i _=> (le_add_of_nonneg_right (sq_nonneg _)).trans_eq (hd i).symm
 have hX: accepts s R univ x=accepts s R B x+cash V^2:=by
    have ht: ∑ i∈ Bᶜ,coreP i = cash V ^2:=by
       rw [pay]; apply (Eq.trans ?_ (sum_subset (f:=fun i=>‖V i‖^2) (subset_univ Bᶜ) (fun i _ p=>by simp [V,show i∈B by simpa using p]))) -- tune
       apply sum_congr rfl; intro i p; have he : i∉ B:= mem_compl.mp p; rw [hd,show Y i=0 from empty_curl x i i (w:=w) (by rw [separation_self]; omega) hx he,norm_zero,show V i=_ from if_pos he]; simp
    change ∑ i,coreP i=_; rw [← ht]; exact (_root_.Eq.symm (sum_add_sum_compl B _)) -- tune
 have hy: cash V^2 ≤ primeShare w s * accepts s R univ x:= H.trans (mul_le_mul_of_nonneg_left hm hδ)
 rw [hX] at hy ⊢; linarith only [hy]
-- Color arrays. Interpolation ledger includes all possible trunks too, specialized geometry next.
abbrev Plush(G:Gauge)(I:Finset (Bond n)) := (↥I)×G.ColorIndex
def tabKey(I:Finset (Bond n))(i:↥I): LT n:= markZ n i
lemma tab_in(I:Finset (Bond n)): Injective (tabKey I):= fun i j h=>Subtype.ext (mark_ins h)
-- active shape
abbrev KickC (I:Finset (Bond n))(x:coin (Plush G I))(i:G.ColorIndex):coin (LT n):= foot (tabKey I)*ᵥ (fun j:↥I=>x (j,i))
def kickC (I:Finset (Bond n))(x:coin (Plush G I)) : LogField G n:= fun j:LT n=> WithLp.toLp 2 (fun i=> KickC I x i j)
lemma at_tab(x:coin (Plush G I))(i:↥I): kickC I x (markZ n i)= WithLp.toLp 2 (fun s=>x (i,s)):=by ext j; exact hold (tabKey I) (tab_in I) (fun u=>x (u,j)) i
lemma at_key(x:coin (Plush G I))(i:Bond n)(p:i∉ I): kickC I x (markZ n i)=0:=by ext j; exact blankA (tabKey I) _ (by rintro ⟨b,t⟩; exact p (mark_ins t ▸ b.2)) (fun u=>x (u,j))
def keyM(G:Gauge)(I:Finset (Bond n)): coin (Plush G I)→ₗ[ℝ] LogField G n where
 toFun:= kickC I
 map_add' x y:=by ext i j; change KickC I (x+y) j i= KickC I x j i +KickC I y j i; exact congr_fun (mulVec_add ..) i -- tune
 map_smul' c x:=by ext i j; change KickC I (c•x) j i=c*KickC I x j i; exact congr_fun (mulVec_smul ..) i
lemma wholeC(h: Floor P φ₀ n a C) (W:R.Bounds φ₀ s.width s.paths Λ)(q:Attached P R)(x:LogField G n): accepts s R univ x=Bid.gaugeFiscal P x x:=by
 rw [metric_pair P W q _ _ h]; apply sum_congr rfl; intro i _; rw [Fintype.sum_bool]; change ‖ellLine R i x‖^2+ ‖(Real.sqrt s.clip.direct) • faceCurl i x‖^2=_
 rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt s.clip.quadratic_pos.le,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,_root_.add_comm]
section relation
variable {y:LogField G n}{Z:Finset (Site n)}
local notation "τX" => buy Z k
def mirrorC (G:Gauge)(P:Bed)(Z:Finset (Site n))(k:ℕ) := ((chips (Axial.axle n) P).submatrix (tabKey (buy Z k)) (tabKey (buy Z k))) -- tune G unused remove
variable (hintU:k≤M)(hintV:Z⊆ zones n M)
-- handle & all global trunk excluded
include hintU hintV in
lemma noHandle (p:Bond n)(pA:p∈ τX)(d:Axis): p≠ Axial.handle n d:=by
 intro h; subst p; obtain ⟨a,h⟩:=excluded hintV hintU _ ‹_›; change d≠timeAxis ∧ _ at h; change (- step d:Site n) timeAxis ≠ 0 at a; simp [Ne.symm h.1] at a
include hintU hintV in
lemma tabFullA(p:coin (Plush G (buy Z k)))(i:G.ColorIndex): let x:=KickC (buy Z k) p i; tickets (Axial.axle n)*ᵥ x=0 ∧ lasers n*ᵥ x=0:=by
 intro x; have h(j:Bond n)(p': j∉ τX): x (markZ n j)=0:= congr_arg (fun y:G.Color=>y i) (at_key p j p') -- tune
 have he(j:Bond n)(t:j∈ (Axial.axle n).trunks): x (markZ n j)=0:= h j fun hintU'=> (excluded hintV hintU j hintU').2.2 t
 constructor
 · rw [tickets_bill]; exact funext fun j=> he j.val j.2
 exact funext fun j=> (tight x j he).trans (h _ (fun t=> noHandle hintU hintV _ t j rfl))

def chrome (G:Gauge)(P:Bed)(Z:Finset (Site n))(k:ℕ):= mirrorC G P Z k ⊗ₖ (1:sp G.ColorIndex)
lemma chrome_eraP(V: sp (↥I))(q:coin (Plush G I)): dotProduct q ((V ⊗ₖ (1:sp G.ColorIndex))*ᵥ q) = ∑ i:G.ColorIndex,dotProduct (fun j:↥I=> q (j,i)) (V*ᵥ (fun j:↥I=>q (j,i))):=by
 have he(i:Plush G I) : ((V ⊗ₖ (1:sp G.ColorIndex))*ᵥ q) i=(V*ᵥ (fun j:↥I=>q (j,i.2))) i.1:=by
    rw [mulVec,dotProduct,Fintype.sum_prod_type]; refine sum_congr rfl fun j _=> ?_; simp [one_apply]
 simp_rw [dotProduct, he,Fintype.sum_prod_type]; rw [sum_comm]
include hintU hintV in
lemma mirror_era (W:R.Bounds φ₀ s.width s.paths Λ)(q:Attached P R)(z:Floor P φ₀ n a C)(x:coin (Plush G (buy Z k))):
 (1-primeShare w s) * dotProduct x (chrome G P Z k*ᵥ x) ≤ accepts s R (billsC k w Z) (kickC (buy Z k) x):=by
 let e:=tabKey τX; let K:=kickC τX x; have hb:= bookShare K (show bid τX K from at_key x) (w:=w) W; rw [wholeC z W q] at hb
 suffices he: Bid.gaugeFiscal P K K=dotProduct x (chrome G P Z k*ᵥ x) by rw [← he]; exact hb
 rw [chrome,chrome_eraP]; unfold Bid.gaugeFiscal; apply sum_congr rfl; intro i _; unfold mirrorC; rw [costsA]; let y:= KickC τX x i; change dotProduct y (plaid P n *ᵥ y) = dotProduct y (chips (Axial.axle n) P*ᵥ y)
 obtain ⟨ht,hx⟩:=tabFullA hintU hintV x i; unfold chips; rw [plus_bill,plus_bill,prize_bill,prize_bill, show tickets (Axial.axle n)*ᵥ y=0 from ht,show lasers n*ᵥ y=0 from hx,dotProduct_zero,dotProduct_zero] -- dot twice? same? Axis ≠Free
 simp
lemma live_sigma(G:Gauge)(z:Floor P F n a C)(w0:0<a): (chrome G P Z k).PosDef:=by exact (((chips_live (Axial.axle n) z w0).submatrix (tab_in _)).kronecker PosDef.one)
include hintU hintV in
lemma upDet (z:Floor P F n a C)(w0:0<a) (G:Gauge) : let c:=Fintype.card G.ColorIndex; (chassis P n)^c≤ (chrome G P Z k).det * ((sheetB C)^ (3*Fintype.card (Site n)+1-(buy Z k).card))^c:=by -- tune optional
 intro c; let q(i:↥(buy Z k)): FreeA n:=⟨i.val,(excluded hintV hintU i i.2).2.2⟩; have hp: (kindleG P n).submatrix q q= mirrorC G P Z k:=by rw [kindleSP]; rfl
 have he:Injective q:= fun i j h=>Subtype.ext (congr_arg (fun i:FreeA n=>i.val) h); unfold chrome; rw [det_kronecker,det_one,one_pow,mul_one,←mul_pow]; apply pow_le_pow_left₀ (chassis_p z w0).le; have hy:=paneBudget q he z w0; rw [hp,Fintype.card_coe] at hy; exact hy
section
variable (g:LogField G n)(hW:R.Bounds s.clip s.width s.paths Λ)(hA:Attached P R)
-- cash of field projected to this active support. ZERO elsewhere for range interface.
abbrev Portion(n:Side)(G:Gauge):=PiLp 2 (fun i:Pressure.Twin n=> G.Color)
def activeM(g:LogField G n)(s:Stage)(P:PathData G)(Y:Finset (Cell n)): Portion n G:=WithLp.toLp 2 (fun i=> if i.1∈ Y then xLin s.clip P g i else 0)
-- linearity
variable (Y:Finset (Cell n))
def heatC (Y: Finset (Cell n))(hW:R.Bounds φ₀ s.width s.paths Λ)(hA:Attached P R) : LogField G n→ₗ[ℝ] Portion n G where -- include params
 toFun:= fun g=> activeM g s R Y
 map_add' g y := by
    ext i j; change (if i.1 ∈ Y then xLin φ₀ R (g+y) i else 0) j=(if i.1∈Y then xLin φ₀ R g i else 0) j+(if i.1∈Y then xLin φ₀ R y i else 0) j; by_cases he:i.1∈Y <;> simp only [he,↓reduceIte,PiLp.zero_apply,_root_.add_zero]
    simp_rw [xLin_component _ _ _ hW hA]; exact congr_fun (mulVec_add ..) _
 map_smul' c g := by
    ext i j; change (if i.1∈Y then xLin φ₀ R (c•g) i else 0) j=c*(if i.1∈Y then xLin φ₀ R g i else 0) j; by_cases he:i.1∈Y <;> simp only [he,↓reduceIte,PiLp.zero_apply,mul_zero]
    simp_rw [xLin_component _ _ _ hW hA]; exact congr_fun (mulVec_smul ..) _
lemma attainedE : ‖heatC Y hW hA g‖^2 = accepts s R Y g:=by
 change cash _^2=_; rw [pay,Fintype.sum_prod_type]; unfold accepts; symm; refine Eq.trans ?_ (sum_subset (subset_univ Y) ?_); swap; · intro j hu hv; simp [hv] -- tune
 apply sum_congr rfl; intro i p; apply sum_congr rfl; intro j _; simp [p] -- tune
end
include hintU hintV in
theorem offer (g:LogField G n)(Q:Floor P φ₀ n a C)(hW:R.Bounds φ₀ s.width s.paths Λ)(hA:Attached P R) (w:ℕ):∃ y:coin (Plush G (buy Z k)),∀ x:coin (Plush G (buy Z k)), (1-primeShare w s)* dotProduct (x+y) (chrome G P Z k*ᵥ (x+y)) ≤ accepts s R (billsC k w Z) (g+ kickC (buy Z k) x):=by
 let B:= billsC k w Z; let L:= heatC B hW hA; let H:=keyM G τX; let V:=LinearMap.range (L.comp H); let K:=V.starProjection
 obtain ⟨y,hy⟩:=show K (L g)∈V from V.starProjection_apply_mem _; change L (H y)=K (L g) at hy; refine ⟨y,fun x=>?_⟩
 have he: K (L (H x))=L (H x):=Submodule.starProjection_eq_self_iff.mpr (show L (H x)∈V from ⟨x,rfl⟩)
 have hp:L (H (x+y))=K (L (g+H x)):=by simp only [map_add,he,hy]; rw [add_comm (L (H x))]
 refine (mirror_era hintU hintV hW hA Q (x+y)).trans ?_; rw [←attainedE _ hW hA B,←attainedE _ hW hA B]; change ‖L (H (x+y))‖^2≤ ‖L (g+H x)‖^2; rw [hp]; exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le ..) 2
end relation
end Haute
end YM.SU5.FiniteGaugeData.Galope
