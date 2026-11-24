import SatinPP.Atelier
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(g:Test4)



def preposition (a:Axis)(c:ℝ)(g:Test4):Test4:= ahead (-c • basis a) g
variable (B:H.Op)
lemma velvet_value(c:ℝ):
  velvet S g c B = valise S B (preposition a c g):=by
 have r:rev a zero_lt_one g=g:=by
    ext1 p
    have u:(reelT a 1) p=p:=by ext i; simp[reelT]
    simpa only [u,ofReal_one,inv_one,one_mul] using revP a zero_lt_one g p
 unfold preposition velvet
 rw [coat_edge _ _ _ _ _ zero_lt_one,r,mul_one,mul_one,←precursor]
 unfold optx; rw[neg_smul,neg_neg,timeslot,←neg_smul,timeslot]

def blockade (u:ℝ) : Bench S→ₗ[ℂ] Bench S:=park S (S.E u.toNNReal) (autumn S _ (cupE S _).symm)
lemma blockade_val(u:ℝ)(y:Bench S):(blockade S u y).val=S.E u.toNNReal y.val:=rfl
lemma blockade_pay(u:ℝ)(y:Bench S)(d:ℕ):
 hall S d (blockade S u y)= S.E u.toNNReal (hall S d y):=
  park_κ S _ _ _ _ _ ((cupE S _).symm.pow_right d)
#print reelT
#print Probe.ahead


lemma wear {d:ℕ}{M:H.Op}{l u c:ℝ}
 (r:Cache S d*M*Cache S d=S.E (c-l).toNNReal*velvet S g c B*S.E (u-c).toNNReal)
 (y:Bench S):
 M y.val = (blockade S (c-l) ((ℑ S B (preposition a c g) d)
           (blockade S (u-c) y))).val:=by
 apply cache_I S d
 have h(z:ℝ)(f:H):
      Cache S d (S.E z.toNNReal f)=S.E z.toNNReal (Cache S d f) := DFunLike.congr_fun
         ((cupE S z.toNNReal).pow_left d).eq f
 conv_rhs =>
    rw [blockade_val,h,Hierarchy.Seld.native,blockade_pay,←velvet_value]
 exact (congrArg (fun x:H=>Cache S d (M x)) (releases S d y).symm).trans (DFunLike.congr_fun r (hall S d y))

lemma prepos_support(c:ℝ)(p:E4)(h:p∈tsupport (preposition a c g)):
   p- (-c • basis a)∈tsupport g:=by
 haveI:(𝓝[support (preposition a c g)] p).NeBot:=mem_closure_iff_nhdsWithin_neBot.mp h
 refine (isClosed_tsupport g).mem_of_tendsto
    ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s:=support (preposition a c g)) (a:=p))) ?_
 filter_upwards [self_mem_nhdsWithin] with y e
 exact subset_closure (show y- _∈support g from e)

-- storage
local notation "W"=>Bench S
local notation "Act"=> (↥(W)→ₗ[ℂ]↥(W))
variable {g S B}
variable (S B) in
inductive Needle (Z:Set E4)(δ l u:ℝ)(d:ℕ):ℝ→H.Op→Act→Prop
 | nil(e:ℝ)(h:0≤e):Needle Z δ l u d e 0 0
 | stitch
 {e:ℝ}{X:H.Op}{L:Act}
 (s: Needle Z δ l u d e X L)
 (f:Test4)
 (space:∀p∈tsupport f,∃z∈Z,∀i:Axis,i≠a→p i=z i)
 (time:∀p∈tsupport f,|p a|<δ)
 (c:ℝ)(h:c∈Ioo l u)(b:ℝ)(pay:‖valise S B f‖≤b)
 (M:H.Op)
 (thermal:∀y:Bench S, M y.val=(blockade S (c-l) ((ℑ S B f d)
           (blockade S (u-c) y))).val)
 : Needle Z δ l u d (b+e) (M+X)
   ((border S c).comp ((ℑ S B f d).comp (border S (-c)))+L)

lemma Dress.act{Z δ l u d e X}(p:Dress (S:=S) Z δ l u B d e g X):
  Needle S B Z δ l u d e X (ℑ S B g d):=by
 change Needle _ _ _ _ _ _ _ _ _ (σV S B d g)
 induction p with
 | @nil g z e h =>
    have i:g=0:=by ext1 y;exact z y
    rw[i,map_zero];exact .nil e h
 | @stitch e g M p g₀ f s c t v b cost h N y ih =>
    have h₀:g₀=f+g:=by ext1;exact (h _).symm
    have q:σV S B d f=(border S c).comp ((ℑ S B (preposition a c f) d).comp (border S (-c))):=by
        ext1 x
        change ℑ S B f d x=usher S (c•basis a) (ℑ S B _ d (usher S (-c•basis a) x))
        rw[attends,ushe,neg_smul,add_neg_cancel,uh_zero]
        have t:(ahead (c • basis a)) (preposition a c f)=f:=by
           ext1 p;change f (p-c • basis a -(-c • basis a))=f p;simp
        rw[t]
    rw[h₀,map_add,q]
    refine Needle.stitch ih (preposition a c f) ?_ ?_ c t b ?_ N (fun j=>wear S f B y j)
    · intro x hx
      exact ⟨_,s (prepos_support f c x hx),fun i q=>by simp[q]⟩
    · intro x hx
      simpa using v _ (prepos_support f c x hx)
    rwa [←velvet_value]
#print Needle

variable (S) in
def Silken (Y:Spool H)(g:Test4)(A:Stamp H)(l u:ℝ):Prop:=
 ∃ X:ℕ→H.Op,
   (∀ n:ℕ, Needle S Y.cell (tsupport g) ((n+1:ℝ)⁻¹) l u Y.d (vial g*‖Y.cell‖) (X n) (Y.Mink S g)) ∧
   Tendsto X atTop (𝓝 (voyage S A l u 1 g))
lemma silk_dress {Y:Spool H}{m:ℕ}{k:ℝ}{A:Stamp H}{l u:ℝ}
 (h:Y.Token S A)(r:Paid S m k A)(p:Band a l u g):
 Silken S Y g A l u:=by
 classical
 choose b i j using (fun n:ℕ=>dressable h r p (show 0<((n+1:ℝ)⁻¹) by positivity))

 refine ⟨b,fun n=>(i n).act,?_⟩
 have t:Tendsto (fun n:ℕ=>vial g*(n+1:ℝ)⁻¹) atTop (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=vial g)).mul (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ (1:ℝ) tendsto_natCast_atTop_atTop))
 exact tendsto_iff_dist_tendsto_zero.mpr (by simp_rw [dist_eq_norm]; exact squeeze_zero (by exact fun _=>norm_nonneg _) j t)

#check tendsto_atTop_add_const_right
