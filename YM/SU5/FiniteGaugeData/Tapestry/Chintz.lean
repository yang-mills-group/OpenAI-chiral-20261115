import YM.SU5.FiniteGaugeData.Tapestry.PalmCourt
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 470000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)

/-!
# Simultaneous receipts, including the bill for mixed products on the
whole admitted paths, at EACH fixed height/footprint.
-/
set_option quotPrecheck false

-- specialize factor spaces once here.
variable (K:Calibration)
section
variable (Λ: Preparation) (l:ℕ)(S:BillOfWork)(n:ℕ)
local notation "𝕌" i:max => Swatch (frameBudget S Λ l i)
local notation "𝕂" i:max=> Swatch (S i)
variable (X Y:QuiltLinks S Λ l) (F D:ℕ→ℝ) (g:∀i, 0 ≤ F i) (w:∀i,0 ≤ D i)(p:ℝ)
def incomeX (T U:Finset Cover) : ℝ:= spread U^2*spread T
lemma incomePositive (T U:Finset Cover): 0 ≤ incomeX T U := by unfold incomeX spread; positivity
lemma matr (x:𝕌 (n+1))(y:𝕂 (n+1)) {C:ℝ}(p:‖x‖≤C):
    ‖material K S n Λ l x y‖ ≤ incomeX (S (n+1)) (frameBudget S Λ l (n+1))*C*‖y‖:=by
 rw [material_eq]; let M:=S (n+1); let T:=frameBudget S Λ l (n+1); let f:= extendRight K S (n+1) Λ l; let V:= spread T; let U:= spread M
 have hf: ‖f y‖ ≤ U*‖y‖:=broadNorm K _ _ (frame_open S (n+1) Λ l) y
 apply (brocadeBound K T x (f y)).trans
 change V^2*‖x‖*‖f y‖≤ V^2*U*C*‖y‖; calc
   _ ≤ V^2*C * (U*‖y‖):= mul_le_mul (mul_le_mul_of_nonneg_left p (sq_nonneg V)) hf (norm_nonneg _) (mul_nonneg (sq_nonneg V) ((norm_nonneg x).trans p))
   _ = _:= by ring
-- first initialization is identity but expensive; use actual CLM cost
def hill (n:ℕ):ℝ:= match n with
 | 0=>‖buildStart S Λ l‖
 | i+1=> incomeX (S (i+1)) (frameBudget S Λ l (i+1))* D i * hill i
-- doesn't take K
def rollFee (n:ℕ):ℝ:= match n with
 | 0=>0
 | i+1=> incomeX (S (i+1)) (frameBudget S Λ l (i+1))*(F i*hill Λ l S D i+ ‖Y i‖* rollFee i)
include w
lemma postal : 0≤ hill Λ l S D n:=by induction n with|zero=> exact norm_nonneg (buildStart S Λ l)| succ n ih=> exact mul_nonneg (mul_nonneg (incomePositive ..) (w n)) ih
include g
lemma supplies:0≤ rollFee Λ l S Y F D n:=by induction n with| zero=> exact le_refl _| succ n ih=> exact mul_nonneg (incomePositive ..) (add_nonneg (mul_nonneg (g n) (postal Λ l S _ D w)) (mul_nonneg (norm_nonneg (Y n)) ih))
omit w g
lemma seam_cmp {R S T:Finset Cover}{a:ℝ}(p b:Swatch R→L[ℂ] Swatch S)(x:Swatch S→L[ℂ] Swatch T)(h:‖p-b‖ ≤ a) : ‖x.comp p - x.comp b‖ ≤ a*‖x‖:=by
 have ha:0 ≤ a:= (norm_nonneg (p-b)).trans h
 refine (x.comp p-x.comp b).opNorm_le_bound (by positivity) fun i=>?_
 change ‖x (p i)-x (b i)‖ ≤ _
 rw [← show x (p i-b i)= x (p i)-x (b i) from x.toLinearMap.map_sub (p i) (b i)] -- arg?
 have hX: ‖p i-b i‖ ≤ a*‖i‖:= (p-b).le_of_opNorm_le h i
 exact (x.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hX (norm_nonneg x)).trans_eq (by ring))
private lemma boundKit {R T:Finset Cover}(A:Swatch R →L[ℂ] Swatch T)(f:Swatch R){C D:ℝ}(p:‖A‖ ≤ C)(x:‖f‖ ≤ D): ‖A f‖≤ C*D:= (A.le_opNorm f).trans (mul_le_mul p x (norm_nonneg _) ((norm_nonneg A).trans p))
private lemma forecast {R T:Finset Cover}(p q:Swatch R→L[ℂ] Swatch T)(x y:Swatch R){A B C:ℝ}(h:‖p-q‖≤ C)(t:‖x‖≤ A)(k:‖x-y‖≤ B): ‖p x-q y‖≤ C*A+‖q‖*B:=toBound (V:=Swatch R) (W:=Swatch T) h t k
private lemma pricesLocal {S T:Finset Cover}(p b:Swatch S→L[ℂ]Swatch T){e:ℝ}(h:‖p-b‖ ≤e) :‖p‖ ≤ e+‖b‖:=opPriceBelow (V:=Swatch S) (W:=Swatch T) h le_rfl
variable (h₁:∀i:ℕ,i<n→ ‖X i‖ ≤ D i) (h:∀i:ℕ,i<n→ ‖X i-Y i‖ ≤ p*F i)
include h₁
lemma deliver (x:Employee S): ‖Tapestry.powers K S Λ l X n x‖ ≤ hill Λ l S D n * nectar n x:=by
  induction n with
  | zero => exact (buildStart S Λ l).le_opNorm _
  | succ n ih=> rw [powers_succ]; apply (matr K Λ l S n _ (x _) (boundKit (X n) _ (h₁ n (by omega)) (ih fun i h=>h₁ i (by omega)))).trans_eq; rw [hill,nectar]; ring
include h
lemma deliver_comp (x:Employee S): ‖Tapestry.powers K S Λ l X n x-Tapestry.powers K S Λ l Y n x‖ ≤ p*rollFee Λ l S Y F D n * nectar n x:=by
  induction n with
  | zero=> rw [powers_zero,powers_zero,rollFee]; simp
  | succ n ih=>
    let a:=Tapestry.powers K S Λ l X n x; let b:= Tapestry.powers K S Λ l Y n x
    rw [powers_succ,powers_succ]
    -- avoid nested NormedSpace
    rw [material_eq,material_eq, show brocade K _ _ _-brocade K _ _ _=brocade K (frameBudget S Λ l (n+1)) (X n a-Y n b) (extendRight K S (n+1) Λ l (x _)) from flipV K _ (X n a) (Y n b) (_)]
    rw [←material_eq]; apply (matr K Λ l S n (X n a-Y n b) (x (n+1)) (forecast (X n) (Y n) a b (h n (by omega)) (deliver K Λ l S n X D (fun i t=> h₁ i (by omega)) x) (ih (fun i w=> h₁ i (by omega)) (fun i x=> h i (by omega))))).trans_eq; rw [rollFee,nectar]; ring
where flipV (K:Calibration)(T:Finset Cover)(f g h:Swatch T):brocade K T f h-brocade K T g h=brocade K T (f-g) h:=(map_sub ((brocadeₗ K T).flip h) f g).symm -- note local ad h₁.. check
lemma pay_comp {G H: (Swatch (frameBudget S Λ l n))→L[ℂ]ℂ}{T:ℝ}(q:‖G-H‖≤p*T) (x:Employee S): ‖G (Tapestry.powers K S Λ l X n x)- H (Tapestry.powers K S Λ l Y n x)‖ ≤ p * (T * hill Λ l S D n + ‖H‖ * rollFee Λ l S Y F D n) * nectar n x:=by
 apply (toBound (V:=Swatch (frameBudget S Λ l n)) (W:=ℂ) q (deliver K Λ l S n X D h₁ x) (deliver_comp K Λ l S n X Y F D p h₁ h x)).trans_eq; ring
end

section
variable {Λ: Preparation} {l : ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (D:Exhibition Y H a b I E L B)
variable (S:BillOfWork)(n i k:ℕ)
local notation "κ"=> tent Y H
local notation "Q"=>motionPay Y H S (B:=B)
local notation "V" j:max=> frameBudget S Λ l j
local notation "U" j:max=> Swatch (frameBudget S Λ l j)
local notation "i₁" t:max => a (WedgeStage.vol t)
local notation "k₁" t:max => b (WedgeStage.uv t)
local notation "F"=> propeller
local notation "Ψ" t:max=> palp Y H (i₁ t) (k₁ t) S
namespace Exhibition
def ether (n:ℕ):ℝ:= ‖extendLeft (tent Y H) S n Λ l‖
def staging (A:Clay Λ l)(n:ℕ):ℝ:= ether Y H S n+‖motionPay Y H S (B:=A) n‖
local notation "σ"=> ether Y H S
local notation "τ"=> staging Y H S B
local notation "E'"=> thermodynamic Y H (V n) n D
include D
lemma quoted : ∀ᶠ t in followStage, ‖(palp Y H (a t.vol) (b t.uv) S n)-motionPay Y H S (B:=B) n‖ ≤ propeller t.vol * ether Y H S n:=by
 filter_upwards [D.cone_bill Y H (V n) n] with t e
 exact seam_cmp (coupon Y H (V n) n (i₁ t) (k₁ t)) (B (V n) n) (extendLeft κ S n Λ l) e.2
lemma sequins : ∀ᶠ t in followStage, ‖palp Y H (a t.vol) (b t.uv) S n‖ ≤ staging Y H S B n:=by
 filter_upwards [D.quoted Y H S n] with t e
 have v:F t.vol ≤ 1:= pow_le_one₀ (by norm_num) (by norm_num)
 have h:‖palp Y H (i₁ t) (k₁ t) S n-Q n‖≤ether Y H S n:= e.trans (mul_le_of_le_one_left (norm_nonneg (extendLeft κ S n Λ l)) v)
 exact pricesLocal ((Ψ t) n) (Q n) h
-- include geom qualifications through all levels ∀
structure Pavilion (Y:Course Λ (VolumeCape.Dream.Nimbus l))(S:BillOfWork)(n i k:ℕ):Prop where
 payZ : Tapestry.Pay Y n i k
 admit : ∀ j<n, Spanned Y (frameBudget S Λ l j) j i k
 tipW : ∀ j≤n, Roomy (frameBudget S Λ l j) (side Y i j)

lemma awarded : ∀ᶠ t in followStage,Pavilion Y S n (i₁ t) (k₁ t):=by
 filter_upwards [(eventually_all_finset (Iic n)).mpr (fun i v=> (D.uniformRoad Y H (V i) i).and (D.uniformRoom Y H (V i) i)),D.payStage Y H n] with t h v -- mp direction?
 exact ⟨v,fun j u=>(h j (mem_Iic.mpr u.le)).1,fun j u=>(h j (mem_Iic.mpr u)).2⟩

def Hank (B:Clay Λ l):= hill Λ l S (staging Y H S B) n
def ArcFee (B:Clay Λ l):= rollFee Λ l S (motionPay Y H S (B:=B)) (ether Y H S) (staging Y H S B) n
omit D
lemma Hank_pos (B:Clay Λ l) : 0≤ Hank Y H S n B:= postal Λ l S n _ (fun n => add_nonneg (norm_nonneg (extendLeft κ S n Λ l)) (norm_nonneg (motionPay Y H S (B:=B) n))) -- κ
lemma ArcFee_pos (B:Clay Λ l): 0 ≤ ArcFee Y H S n B:= supplies Λ l S n (motionPay Y H S (B:=B)) (ether Y H S) (staging Y H S B) (fun n=>norm_nonneg (extendLeft κ S n Λ l)) (fun n => add_nonneg (norm_nonneg (extendLeft κ S n Λ l)) (norm_nonneg (motionPay Y H S (B:=B) n)))
def Garland : ℝ:= spread (frameBudget S Λ l n) * Hank Y H S n B+ ‖thermodynamic Y H (frameBudget S Λ l n) n D‖ * ArcFee Y H S n B
include D
lemma Garland_pos: 0≤ Garland Y H D S n:= add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Hank_pos ..)) (mul_nonneg (norm_nonneg (thermodynamic Y H (frameBudget S Λ l n) n D)) (ArcFee_pos ..))
omit D in
lemma powers_payVista (x:Employee S) : ‖outfitView Y H n S x B‖ ≤ Hank Y H S n B * nectar n x:= deliver κ Λ l S n (motionPay Y H S (B:=B)) (staging Y H S B) (fun i h=> le_add_of_nonneg_left (norm_nonneg (extendLeft κ S i Λ l))) x -- maybe order
lemma motifVista {x:Employee S}(p:Clocked (K:=tent Y H) S n x):
    vistaTake Y H D (motif κ S x)=thermodynamic Y H (frameBudget S Λ l n) n D (outfitView Y H n S x B):=by
 rw [vistaCall Y H n _ D (motif_paid κ S x n p),vistaFinish,motif,pureShot, Decking.reckon_paid _ _ _ p,comparedVista,localThermo] -- order proof args
-- plug finite coupon in condition (doesn't need multiproof ell except Pavilion)
omit D in
lemma motifActual (x:Employee S)(c:Clocked (K:=tent Y H) S n x)(p:Pavilion Y S n i k):
    taking Y H i k (motif κ S x) = tapReader Y H (frameBudget S Λ l n) n i k (costumeAt Y H i k n S x):=by
  rw [breathing_fin _ _ _ _ _ _ p.payZ (motif_paid κ S x n c)]; unfold motif;
  rw [breathing_pure _ _ _ _ _ _ c,comparedOutfit Y H i k n S x p.admit, ← ContinuousLinearMap.comp_apply,swatchSavings] -- tune


lemma stage_cost : ∀ᶠ t in followStage,Pavilion Y S n (i₁ t) (k₁ t) ∧ ∀ x:Employee S,
 let M:= costumeAt Y H (a t.vol) (b t.uv) n S x
 ‖M‖ ≤ Hank Y H S n B * nectar n x ∧
 ‖M-outfitView Y H n S x B‖ ≤ propeller t.vol * ArcFee Y H S n B * nectar n x ∧
 (Clocked (K:=tent Y H) S n x→ ‖taking Y H (a t.vol) (b t.uv) (motif κ S x)-D.vistaTake Y H (motif κ S x)‖ ≤ propeller t.vol * Garland Y H D S n * nectar n x):=by
 have s:= D.stability Y H (V n) n
 filter_upwards [s, D.awarded Y H S n,(eventually_all_finset (Finset.Iic n)).mpr fun i x=> (D.quoted Y H S i).and (D.sequins Y H S i)] with t v p q
 have h(x)(u:x<n): ‖palp Y H (i₁ t) (k₁ t) S x‖ ≤ τ x:= (q x (mem_Iic.mpr u.le)).2
 have he(x)(u:x<n): ‖palp Y H (i₁ t) (k₁ t) S x-Q x‖ ≤ F t.vol * σ x:= (q x (mem_Iic.mpr u.le)).1
 refine ⟨p,fun x=> ?_⟩; intro M; refine ⟨deliver κ Λ l S n (Ψ t) τ h x, deliver_comp κ Λ l S n (Ψ t) (Q) σ τ (F t.vol) h he x,fun x' => ?_⟩
 rw [motifActual Y H S n _ _ x x' p, D.motifVista Y H S n x']; exact Tapestry.pay_comp κ Λ l S n (Ψ t) Q σ τ (F t.vol) h he v x
end Exhibition
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.stage_cost
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.powers_payVista
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.motifVista
