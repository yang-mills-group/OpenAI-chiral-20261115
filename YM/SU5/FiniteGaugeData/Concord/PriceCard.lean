import YM.SU5.FiniteGaugeData.Concord.Fortify
/-! # Issue from this very playhouse: prices & the actual mixed multi-resolution read. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
namespace Meet
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable {i k:ℕ→ℕ} (W:Traced Y H i k F E P)
variable (S:ℕ→Finset Cover)(f:∀ i,Palette (S i)) (n d s:ℕ)
local notation "S'"=> spread Λ l S
local notation "K"=> tent Y H
local notation "ν" s:max=> side Y n s

def ground (j:ℕ) : Method Λ l (spread Λ l S j):= screen Y H ((S') j) j n d
def upper (P:Playhouse Λ l)(j:ℕ): Method Λ l (spread Λ l S j):= P.matinee j ((S') j) n
def final (P:Playhouse Λ l)(j:ℕ):Method Λ l (spread Λ l S j):= P.issue j ((S') j)
local notation "q" => ground Y H S n d
local notation "qi"=> upper S n P
local notation "qp"=> final S P

local notation "Z" => stock Λ l S K

def charger (j:ℕ):ℝ:= max 1 (local_post_bound Y H (spread Λ l S j) j).choose
lemma charge : 1 ≤ charger Y H S s:= le_max_left ..
local notation "b₀"=> charger Y H S
lemma ground_cap: ‖ground Y H S n d s‖ ≤ (b₀) s:= (posted ..).trans (le_max_right ..)
include W
lemma upper_cap : ‖upper S n P s‖ ≤ (b₀) s:= by
  have h:= (W.receipts.clocks s ((S') s)).inner n; have h':=Tendsto.norm (E:=Method Λ l ((S') s)) h; apply le_of_tendsto h'; exact Eventually.of_forall fun x=> ground_cap Y H S n (k x) s -- TC TODO
lemma final_cap : ‖final S P s‖ ≤ (b₀) s:= by
  have h:= (W.receipts.clocks s ((S') s)).periods; have h':=Tendsto.norm (E:=Method Λ l ((S') s)) h; apply le_of_tendsto h'; exact Eventually.of_forall fun x=> upper_cap Y H W S (i x) s

omit W
section pure
-- factors at arbitrary junior equality through s
variable (P' : ℕ→junior (tent Y H))
def synch : Prop:=∀ j ≤ s, P' j= music K (S j) (f j)
local notation "xstock"=> music K ((S') s) (stock Λ l S K f (ground Y H S n d) s)
local notation "ρ"=> realizeStage Y H n d s W

lemma crossstage (v:synch Y H S f s P')(t:∀ j<s,SeasonPass Y H ((S') j) j n d) :
    (stagewrap Y H n d s P').val= observe Y H n s (music K ((S') s) (stock Λ l S K f (ground Y H S n d) s)).val:=by
  induction s with
  | zero => rw [stage_begin, v 0 le_rfl, stock_begin]; rfl
  | succ s ih =>
    have he : SeasonPass Y H _ s _ _:= t s (lt_add_one _); have y:= t s (lt_add_one _)
    let U:= swept Λ l ((S') s); let z:= music K ((S') s) ((Z) f (ground Y H S n d) s); let x:=stagewrap Y H n d s P'; let b:= music K U ((ground Y H S n d) s ((Z) f (ground Y H S n d) s)); let c:= music K (S (s+1)) (f (s+1))
    have hv : x.val= observe Y H n s z.val:=ih (fun i e=> v i (by omega)) (fun j t'=>t j (by omega))
    rw [stage_next, stock_next, v (s+1) le_rfl]; change (scenic Y n d s x).val * observe Y H n (s+1) c.val= observe Y H n (s+1) (b.val*c.val)
    rw [ticket_v Y n d s y.timely, hv, observe_mul]; apply congrArg (· * _); unfold b z; rw [music_coe,music_coe, ←nativeHere_eq,←nativeHere_eq, ground, house Y H _ _ y]; exact (repertoire ..).symm
local notation "tensor" f:max=> PiTensorProduct.tprod ℂ f
include W
lemma registered (p:synch Y H S f s P')(e:Style.fits s P')(t:∀ j<s,SeasonPass Y H ((S') j) j n d):
    (realizeStage Y H n d s W (PiTensorProduct.tprod ℂ P')).val= nativeHere Y H n s (spread Λ l S s) (stock Λ l S K f (ground Y H S n d) s):=by rw [stage_e Y H n d s W P' e,nativeHere_eq,crossstage Y H S f n d s P' p t]; rfl
lemma actors (p:synch Y H S f s P')(e:Style.fits s P')(t:∀ j<s,SeasonPass Y H ((S') j) j n d):
    intake Y H s W.own (music K (spread Λ l S s) ((Z) f (q) s))= E s (pigment _ K ((Z) f (q) s)) ∧
    -- first for convenience? remove
    reader Y H n d s W (tensor P')= sharply Y H n s d (spread Λ l S s) ((Z) f (q) s) ∧
    AtSupport false (region (spread Λ l S s) (side Y n s)) ((ρ) (tensor P')).val ∧
    ∀ a, ‖((ρ) (tensor P')).val a‖≤ count ((S') s)*(facia Λ l S s (charger Y H S)*purse S f s) :=by
  rw [reader,registered Y H W S f n d s P' p e t]
  exact ⟨intake_eq ..,rfl,nativeHere_support ..,fun a=>(native_cost ..).trans (mul_le_mul_of_nonneg_left (bound Λ l S K f (q) s (b₀) (charge Y H S) (fun j _=> ground_cap ..)) (count_nonneg _))⟩

lemma font (p:synch Y H S f s P') :
    (Style.prefixTube _ (fun _=> LinearMap.id) (fun s=> courseAdvance Y H s W) s).soc P'= music K ((S') s) ((Z) f (qp) s) :=by
  induction s with
  | zero => rw [Style.curtained, stock_begin]; exact p 0 le_rfl
  | succ s ih=>
    have t:synch Y H S f s P':=fun i e=> p i (by omega)
    rw [Style.vystep, ih t, courseAdvance_on, p (s+1) le_rfl,stock_next]; rfl

lemma issue_font (p:synch Y H S f s P')(v:Style.fits s P') : issue Y H W s (tensor P')=music K ((S') s) ((Z) f (qp) s):= by rw [solo_issue Y H W P' v]; exact font Y H W S f s P' p
end pure
omit W
variable (A B:∀ i,Method Λ l (spread Λ l S i))
-- placeholder reading on stock (limits or valid tagged array only)
def deliver (u:Music (spread Λ l S s)): ℂ:= u (stock Λ l S K f A s)
def matt (g:ℕ):ℂ:= deliver Y H S f s (upper S g P) (gaugeEar Y H ((S') s) s W.own g)
def purseFee (g v:ℕ):ℂ:=deliver Y H S f s (ground Y H S g v) (critic Y H ((S') s) s g v)
def finished :ℂ:=deliver Y H S f s (final S P) (finale Y H ((S') s) s W.own)
local notation "localB"=> (local_cost Y H s ((S') s)).choose

theorem amount (p:∀ i<s,‖A i‖ ≤ (b₀) i) (u:Music (spread Λ l S s)) (k:‖u‖ ≤ localB):
    ‖deliver Y H S f s A u‖ ≤ (localB * facia Λ l S s (b₀))*purse S f s:=by
  apply (u.le_of_opNorm_le k _).trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (bound _ _ S K f A s (b₀) (charge Y H S) p) (xcost ..)

def delta (x e:ℝ):ℝ:= (x+(local_cost Y H s (spread Λ l S s)).choose*s*e)*facia Λ l S s (charger Y H S)
lemma delta_pos {x e:ℝ}(p:0≤x)(r:0≤e):0≤delta Y H S s x e:=mul_nonneg (add_nonneg p (mul_nonneg (mul_nonneg (xcost ..) (Nat.cast_nonneg _)) r)) (facia_size _ _ S s (b₀) (charge Y H S))

theorem quote_diff (p:∀ i<s,‖A i‖ ≤ (b₀) i) (r:∀ i<s,‖B i‖ ≤ (b₀) i)(u v:Music (spread Λ l S s))(k:‖v‖ ≤ localB)
    {x e:ℝ} (xp:0 ≤ x)(ep:0 ≤ e)(i:∀ j<s,dist (A j) (B j) ≤ e)(o:dist u v ≤ x):
    ‖deliver Y H S f s A u - deliver Y H S f s B v‖ ≤ delta Y H S s x e*purse S f s :=by
  let a:= stock Λ l S K f A s; let b:= stock Λ l S K f B s; let C:=facia Λ l S s (b₀)*purse S f s
  have he :‖(u-v) a‖ ≤ x*C:= ((u-v).le_of_opNorm_le (by rw [dist_eq_norm (E:=Music ((S') s))] at o; exact o) a).trans (mul_le_mul_of_nonneg_left (bound _ _ S K f A s (b₀) (charge Y H S) p) xp)
  have hv : ‖v (a-b)‖ ≤ localB*(s*e*C):=(v.le_of_opNorm_le k _).trans (mul_le_mul_of_nonneg_left (price Λ l S K f A s (charger Y H S) (charge Y H S) p B r e ep i) (xcost ..))
  change ‖u a-v b‖ ≤ _; rw [show u a-v b=(u-v) a+v (a-b) from by rw [ContinuousLinearMap.sub_apply,map_sub]; abel]
  exact (norm_add_le ..).trans ((add_le_add he hv).trans_eq (by unfold C delta; ring))

include W
variable (P' : ℕ→junior (tent Y H))(p:synch Y H S f s P')(e:Style.fits s P')
include p e
lemma finished_eq : finished Y H W S f s= starGem Y H W s (PiTensorProduct.tprod ℂ P'):=by
 rw [starGem, issue_font _ _ W S f s P' p e]; exact (intake_funds ..).symm
lemma weighed (t:∀ j<s, SeasonPass Y H ((S') j) j n d)(r:Ready Y H ((S') s) s n d):
    purseFee Y H S f s n d=reader Y H n d s W (PiTensorProduct.tprod ℂ P'):= (onPitch _ _ _ _ r _).trans (actors Y H W S f n d s P' p e t).2.1.symm
end Meet
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.Meet.finished_eq
#print axioms YM.CF.Buffered.Concord.Meet.weighed
#print axioms YM.CF.Buffered.Concord.Meet.quote_diff
