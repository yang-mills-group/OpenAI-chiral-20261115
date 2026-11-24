import YM.CF.BProof.Moment.Priced
import YM.CF.BProof.Site.Micro
import YM.RG.Bounded

/-! Aggregated weak supports. A Support is always a nonempty connected micro set on
nonzero terms. Use all linked supports (allow zero). Control finite prices. Arguments may
be arbitrary fields (no projected geometry needed yet). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Moment
open Filter Set RG Wilson Lattice Finset Function Push.AbsoluteSums MeasureTheory Micro
open scoped Topology BigOperators Classical
variable {A:Type} {G:Gauge}{s:Side}
-- not confuse Physical labels
structure Bill (s:Side) (G: Gauge) where
 amount : Support s→ ℝ
 tax : Support s→ Config G s→ℝ
 meas T : Measurable (tax T)
 stops (T:Support s) : Lattice.LocalOn T (tax T)
 owned T : GaugeInvariant (tax T)
 enough T U : ‖tax T U‖ ≤ amount T
 roots T (h:amount T≠0) : T.Nonempty ∧ Micro.Loc T
namespace Bill
variable (B:Bill s G)(U:Config G s)
def price := ∑ T,B.tax T U
lemma amount_p T : 0≤B.amount T:= le_trans (norm_nonneg _) (B.enough T (1:Config G s))
lemma tax_ep T : Envelope (B.tax T):= ⟨B.meas T,_ ,fun x=> B.enough T x⟩
def combine (D: Bill s G) : Bill s G where
 amount T:= B.amount T+D.amount T
 tax T:= fun U=> B.tax T U + D.tax T U
 meas T:= (B.meas T).add (D.meas T)
 stops T U V h:= congrArg₂ (·+·) (B.stops T U V h) (D.stops T U V h)
 owned T t U:= by dsimp only; rw [B.owned T t U,D.owned T t U]
 enough T U:= (norm_add_le ..).trans (add_le_add (B.enough T U) (D.enough T U))
 roots T h:=by by_cases a:B.amount T=0; exact D.roots T (by simpa [a] using h); exact B.roots T a
lemma combine_price (D: Bill s G): (B.combine D).price U=B.price U+D.price U:=sum_add_distrib ..

def fine (r C:ℝ):= Toll id B.amount r C
lemma combine_fine (D:Bill s G){r C K:ℝ}(h:B.fine r C)(g:D.fine r K): (B.combine D).fine r (C+K) :=by
 refine ⟨(B.combine D).amount_p,fun i=>?_⟩; convert budget_plus (h.pays i) (g.pays i) using 1; ext x; unfold hit combine; split; rw [mul_add]; simp
end Bill

variable [Countable A]
structure Letters (G:Gauge)(s:Side)(A:Type) where
 foot : A→ Support s
 map : A→ Config G s →ℝ
 size : A→ℝ
 spot i : (foot i).Nonempty
 loc i : Micro.Loc (foot i)
 pushes i : Lattice.LocalOn (foot i) (map i)
 kept i : GaugeInvariant (map i)
 meas i : Measurable (map i)
 weight i V: ‖map i V‖≤size i
 saved : Summable size
namespace Letters
variable (L:Letters G s A)
lemma sum_point (U:Config G s) : Summable (fun i=>L.map i U):=Summable.of_norm_bounded L.saved (fun i=> L.weight i U)
def lump (T:Support s)(x:Config G s)(i:A):= if L.foot i=T then L.map i x else 0
def mon (T:Support s)(i:A):= if L.foot i=T then L.size i else 0
lemma mon_p (T:Support s)(i:A):0≤L.mon T i:=by unfold mon; split; exact le_trans (norm_nonneg _) (L.weight i (1:Config G s)); exact le_rfl
lemma mon_v (T:Support s):Summable (L.mon T):= by rw [show L.mon T={i| L.foot i=T}.indicator L.size by ext x; simp [mon,indicator]]; exact L.saved.indicator _
lemma lump_p (T U i) : ‖L.lump T U i‖ ≤ L.mon T i:=by unfold lump mon; split; exact L.weight i U; rw [norm_zero]
lemma lump_v (T:Support s)(U:Config G s): Summable (fun i=>L.lump T U i):=Summable.of_norm_bounded (L.mon_v T) (fun i=>L.lump_p ..)

def charge : Bill s G where
 amount T := ∑' i,L.mon T i
 tax T U:=∑' i,L.lump T U i
 meas T := by apply Measurable.tsum; intro i; unfold lump; split; exact L.meas i; exact measurable_const
 stops T U V h:= tsum_congr fun i=> by unfold lump; split; rename_i e; exact L.pushes i U V (e ▸ h); exact rfl
 owned T g U:=tsum_congr fun i=> by unfold lump; split; exact L.kept i g U; exact rfl
 enough T U:= (norm_tsum_le_tsum_norm ((L.lump_v T U).norm)).trans (Summable.tsum_mono ((L.lump_v T U).norm) (L.mon_v T) (fun i=>L.lump_p ..))
 roots T h:=by
   by_contra u; apply h; rw [show L.mon T=fun _=>0 from funext fun i=> if_neg (fun (e:L.foot i=T)=> u (e ▸ (show (L.foot i).Nonempty∧Micro.Loc (L.foot i) from ⟨L.spot i,L.loc i⟩))), tsum_zero]
lemma recorded (U:Config G s): L.charge.price U= ∑' i,L.map i U:=by
 change ∑ T: Support s,(∑' i,L.lump T U i)=_
 rw [← Summable.tsum_finsetSum (fun T _=> L.lump_v T U)] -- name?
 exact tsum_congr fun i=> by simp [lump,eq_comm]
lemma fine {r C:ℝ}(h:Toll L.foot L.size r C) : L.charge.fine r C:= Toll.pool _ _ L.foot id rfl h _ (fun i=> by convert (L.mon_v i).hasSum using 1 <;> first| rfl| (congr!; simp [mon]))
end Letters
end YM.CF.BProof.Moment
