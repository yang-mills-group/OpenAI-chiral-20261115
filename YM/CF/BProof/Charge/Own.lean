import YM.CF.BProof.Charge.Input
import YM.CF.BProof.Angular.Faces

/- Charge ownership at all ordinary fields, including inactive marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Push.AbsoluteSums Work Micro Moment MeasureTheory Angular Angular.Yard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}{G:Gauge} (Y:Yard s)(i:Y.Index)(c:Clip)(p:BudgetPoint)(T:PathData G)(M:ℕ)(β:ℝ)(U : Config G s)
-- exact splitting
abbrev Tile (s:Side):= Cell s ⊕ Lam s
def tomb := univ.filter (fun x:Cell s=> touched x⊆ Y.band i)
def ColdQ (x:Site s) := ∀ j:Y.Index,¬Y.Vic j (4*M) (time x)
def steeple := univ.filter (fun a:Lam s=> ColdQ Y M a.center ∧ Y.twinsBand (time a.center)=i)
def Coop (S:Support s):= ∃ i, S.Nonempty ∧ S⊆ Y.band i
def stable := univ.filter (fun S:Support s=> S.Nonempty ∧ S⊆ Y.band i)
def coldG (z:Tile s):Prop:= Sum.elim Y.Marked (fun i=>ColdQ Y M i.center) z

def heavy (z:Tile s) := Sum.elim (directQ c p β U) (higher c p T M β U) z
lemma heavy_c (z:Tile s){W C Λ:ℝ}(h:T.Bounds c W C Λ): Measurable (fun U:Config G s=>heavy c p T M β U z):=by cases z; exact direct_c ..; exact higher_c (G:=G) c p T M _ h _ -- tune
lemma heavy_pos (z:Tile s)(h:0≤β) : 0≤heavy c p T M β U z:=by cases z; exact direct_pos _ _ _ U _ h; exact higher_pos _ _ T _ _ U _ h -- tune
lemma distinct {i j:Y.Index}{b:Support s}(g:b.Nonempty)(h:b⊆Y.band i)(u:b⊆Y.band j):i=j:=by obtain ⟨x,a⟩:=g; exact (Y.u_part i _ (mem_strip.mp (h a))).symm.trans (Y.u_part j _ (mem_strip.mp (u a)))
lemma among {x:Cell s}(h:touched x⊆ Y.band i): Y.twinsBand (time x.1)=i:=Y.band_heir (mem_strip.mp (h (four_self _)))

def outlay (B:Bill s G) := (∑ x∈ tomb Y i,directQ c p β U x) +(∑ x∈steeple Y i M, higher c p T M β U x)+(∑ x∈ stable Y i,B.tax x U)
def left (B: Bill s G) := ∑ x:Support s with ¬Coop Y x,B.tax x U
def big := ∑ z:Tile s with ¬coldG Y M z,heavy c p T M β U z
variable {W C Λ:ℝ}(h:T.Bounds c W C Λ)(k:ValidR c p M)(hm:1≤ M)

/-- Restoring the complete physical action. -/
lemma expenditures : let B:=weak c p T M β h k; T.inChannels c p β U=(∑ i,outlay Y i c p T M β U B)+left Y U B+big Y c p T M β U:=by
 let B:=weak (s:=s) c p T M β h k; let o:= directQ c p β U; let u:=higher c p T M β U; let v(x):=B.tax x U
 have H {A:Type} [Fintype A](P:Y.Index→Finset A)(q:A→Prop)(h:∀ a:A,q a↔∃ i,a∈P i)(w:A→ℝ)(hp:∀ a i j,a∈P i→a∈P j→ i=j) : ∑ a,w a=(∑ i:Y.Index,∑ a∈P i,w a)+∑ a,if ¬ q a then w a else 0:=by
    have hv(i):∑ a∈P i,w a=∑ a:A, if a∈P i then w a else 0:= Eq.symm (by rw [←sum_filter]; simp)
    simp_rw [hv]; rw [sum_comm (s:=univ) (t:=univ),← sum_add_distrib]; apply sum_congr rfl; intro a ha; by_cases H' : q a
    · obtain ⟨i,hi⟩:=(h a).1 H'; rw [sum_eq_single i]; simp [hi,H']; intro j hj hh; exact if_neg (fun H=> hh (hp a j i H hi)); simp
    have hk(i):a∉ P i:= fun e=> H' ((h a).2 ⟨i,e⟩); simp_rw [if_neg (hk _),if_pos H',sum_const_zero,zero_add] -- tune
 rw [exact_channels c p T M β U h k]; unfold outlay; change (∑ x,o x)+(∑ a,u a)+(∑ t,v t)=_
 rw [H (tomb Y) Y.Marked (by intro a; simp [Marked,tomb]) o (fun a i j h v=> (among Y i (mem_filter.mp h).2).symm.trans (among Y j (mem_filter.mp v).2)), H (fun i=>steeple Y i M) (fun a:Lam s=>ColdQ Y M a.center) (by intro x; simp [steeple]) u (fun x i j h v=> (mem_filter.mp h).2.2.symm.trans (mem_filter.mp v).2.2), H (stable Y) (Coop Y) (by intro x; simp [stable,Coop]) v (fun a i j h v=> distinct Y (mem_filter.mp h).2.1 (mem_filter.mp h).2.2 (mem_filter.mp v).2.2)]
 unfold left big Tile; rw [Finset.sum_filter (p:=fun z:Cell s ⊕ Lam s=> ¬coldG Y M z)]; simp only [Fintype.sum_sum_type,coldG,heavy,Sum.elim_inl,Sum.elim_inr,sum_add_distrib] -- semis
 rw [sum_filter (p:=fun x=>¬Coop Y x)]; unfold o u v B; abel_nf
 conv_lhs => rhs; rw [add_comm,add_assoc,add_assoc,add_assoc]
 congr!
include h k hm
lemma high_band (x: Lam s)(g:x∈steeple Y i M): LocalOn (Y.band i) (fun U:Config G s=> higher c p T M β U x):=by
 obtain ⟨hv,pq⟩:= (mem_filter.mp g).2; rw [← pq]; intro U V hx; exact higher_local c p T M β h x k _ _ (agrees_mono hx (Finset.coe_subset.mpr ((Corona.halo_mono (by omega) (Finset.Subset.refl _)).trans (Y.seated (4*M) hv))))
lemma outlay_read (B:Bill s G) : LocalOn (Y.band i) (fun U=> outlay Y i c p T M β U B):= by
 intro U V hx; apply congrArg₂ (·+·) (congrArg₂ (·+·) (sum_congr rfl fun x hh=> direct_here c p β x _ _ (agrees_mono hx (Finset.coe_subset.mpr (mem_filter.mp hh).2))) (sum_congr rfl fun x h=>high_band Y i c p T M β ‹_› k hm x h _ _ hx)); exact sum_congr rfl fun x h=>B.stops x _ _ (agrees_mono hx (Finset.coe_subset.mpr (mem_filter.mp h).2.2))
omit k hm
lemma outlay_m (B:Bill s G) : Measurable (fun U=>outlay Y i c p T M β U B):=(((Finset.measurable_sum _ (fun x h=> direct_c c p β x)).add (Finset.measurable_sum _ (fun x h'=>higher_c c p T M β h x))).add (Finset.measurable_sum _ (fun x h=>B.meas x))) -- tune
lemma outlay_g (B:Bill s G)(g:Site s→G.El): outlay Y i c p T M β (Lattice.gauge g U) B = outlay Y i c p T M β U B:=by unfold outlay; simp only [higher_g c p T M β U h, direct_g]; congr 1; exact sum_congr rfl fun x _=> B.owned x g U
end YM.CF.BProof.Charge
