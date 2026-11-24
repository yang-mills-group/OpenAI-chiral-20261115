import YM.SU5.FiniteGaugeData.Tapestry.Chalice
/-! Pocket cost hierarchy: fixed finite changes. Enables shifting boundary
marks with one paid subsequence for actual pre-limit evaluation--not merely
indexed by the interior read. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 6000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry.Pocket
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude Heat Pastry
open PiTensorProduct (tprod)
variable (K: Calibration)(S T: BillOfWork) (n k:ℕ)

lemma increase {W:ℝ}(h:0≤W) (p:∀ (x:Employee S), Clocked (K:=K) S n x → Pocket K T k (W*nectar n x) (motif K S x))
    {x:Cloud (Dome K)}{C:ℝ} (z:Pocket K S n C x) : Pocket K T k (W*C) x := by
  induction z with
  | stone x t=> exact p x t
  | no=> rw [mul_zero]; exact .no
  | shade a _ t=> rw [mul_left_comm W ‖a‖]; exact .shade a t
  | blend _ _ t u=> rw [mul_add]; exact .blend t u
  | fully e _ u=> exact .fully (mul_le_mul_of_nonneg_left e h) u

lemma price_widen (p:∀i,S i⊆ T i): ∃ r:ℝ,0≤r∧∀ x C,Pocket K S n C x→ Pocket K T n (r*C) x:=by
  let f (i:ℕ):= Tapestry.broad K (S i) (T i) (p i); let C:= ∏ i∈ Iic n, ‖f i‖
  have he:0≤C:=Finset.prod_nonneg fun i _=> norm_nonneg (f i)
  refine ⟨C,he,fun x y=>increase K S T n n he ?_⟩
  intro z k; let F:Employee T:=fun i=> f i (z i)
  have hp : employ K T F=employ K S z:=funext fun i=>widenBadge K (S i) (p i) (z i)
  rw [show motif K S z=motif K T F from congrArg (pureShot K) hp.symm]
  have h:= (le_trans (nectarBelow n F (f:=fun i=>‖f i‖* ‖z i‖) (fun i _=> (f i).le_opNorm _)) (Eq.le (show _ = C*nectar n z by rw [prod_mul_distrib,nectar_eq])))
  exact .fully h (.stone F (show Altitude.Enough n (employ K T F) from hp.symm ▸ k))
lemma price_up : ∃ r:ℝ,0≤r ∧ ∀ x C,Pocket K S n C x→ Pocket K S (n+1) (r*C) x:=by
  let f:= colorless K (S (n+1)); refine ⟨‖f‖,norm_nonneg _, fun x y=> increase K S S n (n+1) (norm_nonneg _) ?_⟩
  intro z k
  have he: employ K S z (n+1)=1:= k _ (by omega)
  have hx:z (n+1)=f:=by
    apply render_inj _ K; have ht : badge K (S (n+1)) (z (n+1))= badge K (S (n+1)) f:= he.trans (laureled ..).symm; exact Subtype.ext_iff.mp ht
  convert (.stone z ((show Altitude.Enough n _ from k).taller (show n≤ n+1 by omega)):Pocket K S (n+1) (nectar (n+1) z) (motif K S z))
    using 1; rw [nectar,hx,mul_comm]
lemma price_higher (p:n≤k):∃ r:ℝ,0≤r∧ ∀ x C,Pocket K S n C x→ Pocket K S k (r*C) x:=by
    induction k,p using Nat.le_induction with
    | base=> exact ⟨1,zero_le_one,fun x C y=> by rwa [one_mul]⟩
    | succ k g ih=> obtain ⟨r,h,d⟩:= ih; obtain ⟨s,p,q⟩:= price_up K S k; exact ⟨s*r,mul_nonneg p h,fun x C k=>by rw [mul_assoc]; exact q _ _ (d _ _ k)⟩

lemma increase_product {u:ℝ}(h:0≤u)(b:Cloud (Dome K))(p : ∀ (x:Employee S), Clocked (K:=K) S n x → Pocket K S n (u*nectar n x) (motif K S x*b))
    {x:Cloud (Dome K)}{C:ℝ} (z:Pocket K S n C x) : Pocket K S n (u*C) (x*b) := by
  induction z with
  | stone x q=> exact p x q
  | no=> rw [mul_zero,zero_mul]; exact .no
  | shade a _ t=> rw [mul_left_comm u ‖a‖,Algebra.smul_mul_assoc]; exact .shade a t
  | blend _ _ t v=> rw [mul_add,add_mul]; exact .blend t v
  | fully k _ t=> exact .fully (mul_le_mul_of_nonneg_left k h) t
lemma price_product :∃ r:ℝ,0≤r ∧ ∀ x y C D,Pocket K S n C x→ Pocket K S n D y → Pocket K S n (r*C*D) (x*y):=by
    -- pay via motif bound with linearity
    let g(i:ℕ):ℝ:= (spread (S i):ℝ)^2
    let v:=∏ i∈Iic n,g i
    have hv:0≤v:=prod_nonneg (fun i _=> sq_nonneg _)
    have he (x y:Employee S)(p:Clocked (K:=K) S n x)(h:Clocked (K:=K) S n y): Pocket K S n (v*nectar n x*nectar n y) (motif K S x*motif K S y):=by
       let F:Employee S:=fun i=>brocade K (S i) (x i) (y i)
       have hp: employ K S x* employ K S y=employ K S F:=funext fun i=> (badge_brocade K (S i) (x i) (y i)).symm
       have hf: Altitude.Enough n (employ K S F):=hp ▸ (show Altitude.Enough n _ from (show Altitude.Enough n _ from p).together h)
       have hq:Pocket K S n (nectar n F) (motif K S F):=.stone F hf
       rw [show motif K S x* motif K S y=motif K S F from by unfold motif pureShot; rw [PiTensorProduct.tprod_mul_tprod,hp]]
       refine .fully ?_ hq; refine le_trans (nectarBelow n F (f:=fun i=> g i * ‖x i‖ * ‖y i‖) fun j _ => brocadeBound K (S j) (x j) (y j)) (le_of_eq ?_)
       rw [prod_mul_distrib,prod_mul_distrib,nectar_eq,nectar_eq]
    refine ⟨v,hv,fun x y C D p k=>?_⟩
    rw [show v*C*D=v*D*C from by ring]; apply increase_product K S n (mul_nonneg hv k.priced) y ?_ p
    intro z h
    rw [mul_comm (motif K S z) y,show v*D*nectar n z=v*nectar n z*D from by ring]
    exact increase_product K S n (mul_nonneg hv (licensedN n z)) _ (fun u t=> by rw [mul_comm (motif K S u)]; exact he z u h t) k
lemma price_whole (g : Cloud (Dome K)) (h:g∈FiniteGaugeDataPoly K): ∃ (T:BillOfWork)(k:ℕ)(r:ℝ), n ≤ k ∧ (∀ i:ℕ,S i ⊆ T i) ∧ 0<r ∧ ∀ x C,Pocket K S n C x→ Pocket K T k (r*C) (x*g):=by
    obtain ⟨t,h⟩:= Altitude.curve.mp h; obtain ⟨T,p⟩:= anyWords K t _ h; let k:=max n t; let U(i:ℕ):=S i∪T i
    obtain ⟨v,u⟩:= issued.mp (coin_mono K T U t k (fun i _=> subset_union_right) (le_max_right ..) p)
    obtain ⟨r,h0,b⟩:=price_widen K S U n (fun _=>subset_union_left)
    obtain ⟨s,y,c⟩:=price_higher K U n k (le_max_left ..)
    obtain ⟨w,z,d⟩:=price_product K U k
    have he:0≤v:=u.priced; have hp: 0 ≤ w*v*s*r:= by positivity
    refine ⟨U,k,w*v*s*r+1,le_max_left ..,(fun i=>subset_union_left),by linarith,fun x C p=>?_⟩
    apply Pocket.fully _ (d _ _ _ _ (c x _ (b x C p)) u)
    calc
    _ = w*v*s*r*C := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) p.priced
end YM.CF.Buffered.Afterglow.Tapestry.Pocket
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Pocket.price_whole
