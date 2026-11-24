import Finch.Trunk
import YM.CF.Buffered.Mark
import YM.CF.Chaff.Pulse
import YM.CF.Sour.Lead

/-! First-pane, tag-independent Borel version of rooted matrix instrument. -/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered
-- from Glyph / pact_p
attribute [local instance] Rill.boreKSpace Rill.boreXN
variable {N:Side}{P:SOp N}{o:Seat N}{a b c d v:ℝ}{p:BudgetPoint}{k r:ℕ}
variable (A:Scree.Loom N)(h:Roof N b d r A)(u:0<d)(X:Trunk o P k a v d)

lemma compRoll (A:Scree.Loom N) (h:Roof N b d r A) (X:Soak o P a v d) (u:0<d) :
    Measurable (fun z=> P (profile (A z))) := by
 obtain ⟨F,T,f,l,t,g⟩:=X
 rw [show (fun z=> P (profile (A z)))=fun z=>∑ S:Sa N,F S (roller u h z) from funext fun z=>g (roller u h z)]
 exact Finset.measurable_fun_sum _ fun i _=> (f i).toTicket.cont.measurable.comp (roll_m u h)

include h X u

/-- Read only links in halo k. -/
lemma Trunk.identical (x y:Orbit N)(f:Agrees (halo k {o}) (A x) (A y)) :
    P (profile (A x))=P (profile (A y)) := by
 obtain ⟨F,T,s,t,-,g⟩:=X.home
 change P (roller u h x).val=P (roller u h y).val
 rw [g,g]
 apply sum_congr rfl
 intro S _
 by_cases w:T S=0
 · ext i j
   have e (V:Openc (More N) d) : F S V i j=0:=norm_le_zero_iff.mp (((s S).expo i j).bounded V|>.trans_eq (by rw [w]; rfl))
   rw [e,e]
 obtain ⟨a,c⟩:=t S w
 apply pact_p u h (s S)
 refine agrees_mono f (coe_subset.mpr (fun i v=>halo_spec.mpr ⟨o,mem_singleton_self _,?_⟩))
 exact ((f_then (s S) w).lim _ a _ v).le.trans c.le

omit h X u in
lemma kernelGaugeCopy (A:Scree.Loom N) (h:Roof N b d r A) (u:0<d) (X:Soak o P a v d)
    (x:Orbit N)(t:Seat N→SU.E) :
    P (profile (A (gauge t x.1,threadG t x.2)))=twist (tradew N t) (P (profile (A x))) := by
 obtain ⟨F,T,s,y,m,g⟩:=X
 change P (roller u h (_,_)).val=twist (tradew N t) (P (roller u h x).val)
 rw [g, g,map_sum,roll_g u h t x]
 refine sum_congr rfl fun i _=>?_
 rw [Inter.frame (s i).toTicket.frame t (roller u h x),twist_formula]; rfl

omit h X u in
lemma Trunk.finchModes (X:Trunk o P k a v d)(x:Openc (More N) d)(S:Sa N)(w:halo k {o}⊆ S) :
    cutM (modesIn N S) * P x.val * cutM (modesIn N S)= P x.val := by
 obtain ⟨F,T,s,t,z,g⟩:=X.home
 rw [g,mul_sum,sum_mul]
 apply sum_congr rfl
 intro i _; ext r q
 unfold cutM
 rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
 by_cases e:F i x r q=0
 · rw [e, mul_zero, zero_mul]
 have he:=ne_of_gt ((norm_pos_iff.mpr e).trans_le (((s i).expo r q).bounded x))
 obtain ⟨u,h,f⟩:=((s i).expo r q).triggered he
 obtain ⟨a,b⟩:=t i (fun v=>he (by rw [v]; rfl))
 have y(x)(p:x∈i) : x∈S:=w (halo_spec.mpr ⟨o,mem_singleton_self _, ((u.lim _ a _ p).trans b).le⟩)
 rw [if_pos ((modes_at S r).mpr (y _ h)),if_pos ((modes_at S q).mpr (y _ f)),one_mul,mul_one]

variable (p o) -- rebind
-- K not passed measurements as random tag; fixed arbitrary id. only used for Borel version
noncomputable def markMatrix (A:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(P:SOp N): Pane N → Op (Single N):=
  ({V | pingS p.threshold (halo p.B {o}) V}:Set (Pane N)).indicator
    fun V=> P (profile (A (V,Classical.arbitrary _)))

variable {A p o}

omit X in
lemma readsLinks (s:Pane N)(y:Ids N) (g:pingS p.threshold (halo p.B {o}) s)
    (q:k+r≤p.B)(l:p.threshold≤b) : Agrees (halo k {o}) (A (s,y)) s:=by
  intro i v t; apply h.lamp
  have he : pingS b (halo p.B {o}) s :=fun i x=>(g i x).trans_le l
  refine Disjoint.mono_right ?_ (ping_le he).symm
  refine Subset.trans (Corona.halo_mono le_rfl (insert_subset v (singleton_subset_iff.mpr t))) ?_
  intro j y; obtain ⟨s,w,f⟩:=halo_spec.mp y
  obtain ⟨s₀,w₀,f₀⟩:=halo_spec.mp w
  exact halo_spec.mpr ⟨s₀,w₀,(separation_triangle _ s _).trans (by omega)⟩

-- Q budgets keep separately
variable (q:k+r ≤ p.B)(l:p.threshold ≤ b)
include l q
lemma ink_here (s:Pane N)(y:Ids N)(g:pingS p.threshold (halo p.B {o}) s) :
    markMatrix A p o P s=P (profile (A (s,y))) := by
 unfold markMatrix
 rw [Set.indicator_of_mem (show s∈_ from g)]
 apply Trunk.identical A h u X
 exact fun i v t=>(readsLinks h u _ _ g q l i v t).trans (readsLinks h u _ _ g q l i v t).symm

omit X h u l q in
lemma ink_away (s:Pane N)(g:¬pingS p.threshold (halo p.B {o}) s) :
    markMatrix A p o P s=0:= Set.indicator_of_notMem (show s∉_ from g) _

lemma ink_gauge (V:Pane N)(t:Seat N→SU.E) : markMatrix A p o P (Lattice.gauge t V)=twist (tradew N t) (markMatrix A p o P V):=by
 by_cases w:pingS p.threshold (halo p.B {o}) V
 · let Z:=Classical.arbitrary (Ids N)
   rw [ink_here h u X q l _ (threadG t Z) ((pingB V t).mpr w),ink_here h u X q l _ Z w]; exact kernelGaugeCopy A h u X.pay (V,Z) t
 rw [ink_away _ (mt (pingB V t).mp w),ink_away _ w,map_zero]

lemma ink_local : LocalOn (halo (p.B+12) {o}) (markMatrix A p o P):=by
 intro V W f
 let S:Sa N:= halo p.B {o}
 have he: inspected S ⊆ halo (p.B+12) {o}:=by -- remove i
    apply (Yaw.touchK S).trans; intro j v
    obtain ⟨u,v,x⟩:=halo_spec.mp v; obtain ⟨s₀,w,k⟩:=halo_spec.mp v
    exact halo_spec.mpr ⟨s₀,w,(separation_triangle _ u _).trans (by omega)⟩
 have eq:=Chaff.fenceW S (agrees_mono f (coe_subset.mpr he)) p.threshold
 by_cases g:pingS p.threshold S V
 · let y:Ids N:=Classical.arbitrary _
   rw [ink_here h u X q l _ y g,ink_here h u X q l _ y (eq.mp g)]
   have hu:halo k ({o}:Sa N)⊆ halo (p.B+12) {o}:= Corona.halo_mono (by omega) le_rfl
   apply Trunk.identical A h u X
   exact fun i v t=>(readsLinks h u _ _ g q l i v t).trans ((f _ (hu v) (hu t)).trans (readsLinks h u _ _ (eq.mp g) q l i v t).symm)
 rw [ink_away _ g,ink_away _ (mt eq.mpr g)]

omit l q
lemma ink_envelope (ha:0≤a) (p:BudgetPoint): Envelope (markMatrix A p o P):= by
 unfold markMatrix
 apply Buffered.env_indicator _ ping_o.measurableSet
 refine ⟨(compRoll A h X.pay u).comp (measurable_id.prodMk measurable_const), v, fun U=>norm_U X.pay ha (roller u h (U,_))⟩

lemma ink_spots (p:BudgetPoint)(V:Pane N)(S:Sa N)(w:halo k {o}⊆ S) :
    cutM (modesIn N S) * markMatrix A p o P V * cutM (modesIn N S)= markMatrix A p o P V := by
 by_cases q:pingS p.threshold (halo p.B {o}) V
 · unfold markMatrix; rw [Set.indicator_of_mem (show V∈_ from q)]; exact X.finchModes (roller u h (V,Classical.arbitrary _)) S w
 rw [ink_away _ q, mul_zero, zero_mul]

end YM.CF.Swell
