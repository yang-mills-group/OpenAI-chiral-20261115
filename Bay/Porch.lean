import YM.SU5.Exchange.Stack.Manor
import YM.CF.Buffered.Probes
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


/- Pre-pull through a Cape, with a fixed ticket for the *physical* consultation
   (not Flags/final extensions for ambient-price testing).
   Use radii in gauge Seats throughout. Inspection allowance in native links. -/
open Buffered (modesIn)
abbrev roost {N:Side}(k:ℕ)(o:Seat N):Sa N:=Lattice.halo k {o}
section basic
variable {I:Type*}[Fintype I][DecidableEq I]
def cork (V:Op I):ℝ:=∑ i,∑ j,‖V i j‖
lemma popping {V:Op I}(p:cork V≤0):V=0:=by
 ext i j
 have l(t:I):0≤∑ j, ‖V t j‖:=sum_nonneg fun _ _=> norm_nonneg _
 have a:= (single_le_sum (f:=fun t=>∑ k,‖V t k‖) (fun i _=>l i) (mem_univ i)).trans p
 exact norm_le_zero_iff.mp ((single_le_sum (f:=fun k=>‖V i k‖) (fun _ _=> norm_nonneg _) (mem_univ j)).trans a)

lemma corkSum {ι:Type*}[Fintype ι](V:ι→ Op I): cork (∑ i,V i) ≤∑ i, cork (V i):=by
 unfold cork; simp_rw [Matrix.sum_apply]
 rw [sum_comm (f:=fun (v:ι) i=>∑ j,‖V v i j‖)]
 apply sum_le_sum; intro i _;rw [sum_comm (f:=fun v j=> ‖V v i j‖)]
 exact sum_le_sum fun j _=>norm_sum_le _ _
lemma cork_norm (V:Op I): ‖V‖≤ cork V:=by
  apply schur (fun i j=> ‖V i j‖) _ _ _ (fun _ _=>le_rfl)

  · intro i; exact single_le_sum (f:=fun v=>∑ j, ‖V v j‖) (fun v _=>sum_nonneg fun _ _=>norm_nonneg _) (mem_univ i)
  · intro i; unfold cork; rw [sum_comm]; exact single_le_sum (f:=fun v=>∑ j, ‖V j v‖) (fun v _=>sum_nonneg fun _ _=>norm_nonneg _) (mem_univ i)
  unfold cork; positivity
lemma cork_tc (V:Op I): ‖Matrix.trace V‖≤ cork V:=(norm_sum_le _ _).trans (sum_le_sum fun i _=> single_le_sum (f:=fun j=> ‖V i j‖) (fun _ _=> norm_nonneg _) (mem_univ i))
abbrev sparHere(V:Op I)(S:Finset I):Prop:=∀ i j,V i j≠0 → i∈ S ∧ j∈S
lemma spar0 (S:Finset I):sparHere (0:Op I) S:=by simp only [sparHere];intro i j h;exact (h rfl).elim
lemma spar_cut {V:Op I}{S T:Finset I}(p:sparHere V S)(g:S⊆ T) : cutM T * V * cutM T = V:=by
 ext i j; rw [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
 by_cases h: V i j = 0
 · simp [h]
 rw [if_pos (g (p _ _ h).1),if_pos (g (p _ _ h).2),one_mul,mul_one]
end basic

variable {N:Side}{X:SOp N}{o:Seat N}{a c d:ℝ}{k:ℕ}
local notation "IΩ" => Single N

lemma modes_ch {S:Support (More N)} {i:Single N}: i∈modesIn N S ↔ node i.1.1∈ S:=by simp [Buffered.modesIn,Window.matterSet, Buffered.sitesIn]


/-- *Uniform* sup price and modulus on any pair of continuations, with domain
    comparison cost measured solely on the restricted station. -/
structure BoxPay (X:SOp N)(o:Seat N)(k:ℕ)(c d:ℝ):Prop where
 award (x:Openc (More N) d): cork (X x.val)≤ c
 sees (x y: Openc (More N) d): cork (X x.val-X y.val) ≤ c * (fare (roost k o) x.val y.val/|d|)
 modes(x:Openc (More N) d): sparHere (X x.val) (modesIn N (roost k o))
 cont: Continuous (fun x:Openc (More N) d=>X x.val)
 color: Inter (bail N d) (bail N d) (fun x=>X x.val)

lemma boxSeal (p:Trunk o X k a c d)(u:0≤a) : BoxPay X o k c d:=by
 obtain ⟨F,C,H,g,G,e⟩:=p.home
 have root(S)(t:C S≠0):S⊆ roost k o:=by
   obtain ⟨r,w⟩:=g S t
   intro x j; apply halo_spec.mpr
   refine ⟨o, mem_singleton_self _,?_⟩
   first|exact le_of_lt (lt_trans ((f_then (H S) t).lim x j _ r) w)|exact le_of_lt (lt_trans ((f_then (H S) t).lim _ r x j) w)
 have total:∑ S,ledgerV (C S) ≤ c := (sum_le_sum (fun S (_:S∈univ)=>le_mul_of_one_le_left (show 0≤ ledgerV (C S) from sum_nonneg fun i _=>sum_nonneg fun j _=> (H S).nonn i j) (Branch.rent_one u S))).trans G
 refine ⟨?_,?_,?_,?_,?_⟩
 · intro x; rw [e]; refine (corkSum _).trans ((sum_le_sum fun S _=> ?_).trans total)
   exact sum_le_sum fun i _=>sum_le_sum fun j _=> ((H S).expo i j).bounded x
 · intro x y; rw [e,e,←sum_sub_distrib]
   let L:=fare (roost k o) x.val y.val / |d|; have hn:0≤L:=div_nonneg (fare_t ..) (abs_nonneg _)
   refine (corkSum (fun S=>F S x-F S y)).trans (le_trans ?_ (mul_le_mul_of_nonneg_right total hn))
   simp_rw [cork,ledgerV,sum_mul]

   refine sum_le_sum fun S _=>sum_le_sum fun i _=>sum_le_sum fun j _=>le_trans (((H S).expo i j).variation x y) ?_
   by_cases hv:C S=0
   · simp only [hv, Pi.zero_apply, zero_mul, le_refl]
   apply mul_le_mul_of_nonneg_left _ ((H S).nonn i j)
   exact div_le_div_of_nonneg_right (fare_inc (root S hv) _ _) (abs_nonneg _)
 · intro x;rw [e]
   intro i j n
   obtain ⟨S,t⟩:∃ S,C S i j≠0:= by
     by_contra! hh;rw [Matrix.sum_apply] at n
     exact n (sum_eq_zero fun S _=>norm_le_zero_iff.mp ((((H S).expo i j).bounded x).trans_eq (hh S)))
   have r:= ((H S).expo i j).triggered t
   have l:=root S (fun h=>t (h ▸ rfl))
   exact ⟨modes_ch.mpr (l r.2.1), modes_ch.mpr (l r.2.2)⟩
 · rw [funext e];exact continuous_finsetSum _ fun S _=>(H S).cont
 rw [funext e];intro g x;dsimp only;rw [Finset.sum_mul,Finset.mul_sum]
 exact sum_congr rfl fun S _=>(H S).frame g x

-- The full small-support bill moves, not just bounds on evaluation.
-- Adapted jul_sells.
lemma boxCargo (s:Sweep N)(p:Trunk o X k a c d):Trunk ((boxA s) o) (julStep s X) k a (Tenant.quota^2*c) d:=by
 obtain ⟨F,W,v1,l,u,v⟩:=p.home
 let Q:= (boxA s⁻¹).symm.finsetCongr; let A:= noteU s⁻¹; let V(T):=Mx s d (F T); let B(T): Toll IΩ:= A (W T); let D:=quota; have hx:0 ≤ D:= le_trans (by norm_num: (0:ℝ)≤16) quota_bound
 have pB: (∑ i, Branch.rent a (Q i) * ledgerV (B i)) ≤ D^2*c:=by
   apply le_trans _ (mul_le_mul_of_nonneg_left u (sq_nonneg D)); rw [mul_sum]; apply sum_le_sum; intro i _
   rw [Branch.rent,show (Q i).card=i.card from card_map ..,mul_left_comm]
   apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
   unfold B A noteU ledgerV; simp_rw [normU,mul_sum]
   let L(x y j k:IΩ):= jLL s⁻¹ x j*jLL s⁻¹ y k*W i j k
   change ∑ x:IΩ,∑ y:IΩ,∑ j:IΩ,∑ k:IΩ,L x y j k ≤ _
   simp_rw [sum_comm (f:=fun y (j:IΩ)=> ∑ k:IΩ,L _ y j k)]
   rw [sum_comm]; apply sum_le_sum; intro j _; simp_rw [sum_comm (f:=fun y k=> L _ y j k)]; rw [sum_comm]; apply sum_le_sum; intro k _
   unfold L; simp_rw [←Finset.sum_mul,←Finset.mul_sum]; rw [←Finset.sum_mul]
   refine mul_le_mul_of_nonneg_right ?_ ((v1 i).nonn _ _); exact (mul_le_mul (ρ_K ..) (ρ_K ..) (sum_nonneg fun t _=>norm_nonneg _) hx).trans_eq (by ring)
 refine ⟨jul_sells _ p.pay, V ∘ Q.symm, B ∘ Q.symm,?_,?_,?_,?_⟩
 · rintro i; obtain ⟨i,rfl⟩:=Q.surjective i; rw [comp_apply,comp_apply,Q.symm_apply_apply]; exact mini _ _ _ _ (v1 i)
 · intro i;obtain ⟨i,rfl⟩:= Q.surjective i; rw [comp_apply,Q.symm_apply_apply]; intro h
   have ht:W i≠0:=by intro t;apply h;unfold B A noteU;rw[t];ext;simp
   simp [Q,sitU,l i ht]
 · rw [←Equiv.sum_comp Q];simpa using pB -- avoid simp loop?
 · intro x; let z:=Sour.fog s d x
   change ech s⁻¹ (X z.val)= _
   conv_rhs=>rw [←Equiv.sum_comp Q]
   simp only [comp_apply,Q.symm_apply_apply]
   rw [v z]; unfold ech; rw [singT,win_sum,map_sum]; rfl

-- The first-Pane masked operator matrix; every Cape call can use any tag there.
variable {p:BudgetPoint}{K:Scree.Loom N}

abbrev setAwning(p:BudgetPoint)(o:Seat N):Set (Pane N):={V|pingS p.threshold (roost p.B o) V}
def bayonet(K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N) : Pane N → Op (Single N):= (setAwning p o).indicator (fun V => X (profile (K (V, Classical.arbitrary _))))

lemma chainR {n m:ℕ} (g : k+m≤n) : Lattice.halo k (roost m o) ⊆ roost n o := by
 intro i h;obtain ⟨x,p,t⟩:=halo_spec.mp h; obtain ⟨y,v,w⟩:=halo_spec.mp p
 -- halo_spec separation ?
 exact halo_spec.mpr ⟨y,v,(by first|exact (separation_triangle _ x _).trans ((Nat.add_le_add t w).trans g)|exact (separation_triangle _ x _).trans ((Nat.add_le_add w t).trans (by omega)))⟩
lemma roost_expand {n:ℕ}(g:k≤n):roost k o⊆roost n o:=Corona.halo_mono g le_rfl

structure Clearance (p:BudgetPoint)(K:Scree.Loom N)(k:ℕ)(d:ℝ):Prop where
 dept: 0<d
 glass: ∃ q t d', Roof N t d' q K ∧ p.threshold ≤ t ∧ d' ≤ d ∧ q+k≤p.B

lemma Clearance.light (H:Clearance p K k d){x:Orbit N}(h:x.1∈ setAwning p o) : Agrees (roost k o) (K x) x.1:=by
 obtain ⟨q,t,d',P,g,l,u⟩:=H.glass
 intro i a b;exact P.lamp x.1 x.2 i ((ping_le (show pingS t (roost p.B o) x.1 from fun j v=>(h j v).trans_le g)).symm.mono_right ((Corona.halo_mono (le_refl q) (insert_subset a (singleton_subset_iff.mpr b))).trans (chainR u))) -- ping_le Healthy abbrev .symm?
lemma Clearance.onD (h:Clearance p K k d)(x:Orbit N):Guard (K x) d:=by obtain ⟨_,_,_,P,g,u,_⟩:=h.glass; exact (P.paid x).shrink u
lemma Clearance.priceLen (h:Clearance p K k d):k≤p.B:=by obtain ⟨_,_,_,_,_,_,u⟩:=h.glass;omega
def doPort (h:Clearance p K k d)(x:Orbit N) : Openc (More N) d:= ⟨profile (K x),K x,h.onD x,by simpa using h.dept⟩ -- implicit Stem inferred?


open scoped YM.CF.Buffered
lemma mealGuard {I D V:Type*} [MeasurableSpace I] [MeasurableSpace D] [TopologicalSpace D] [OpensMeasurableSpace D] [MeasurableSpace V] [TopologicalSpace V] [BorelSpace V]
    {f:I→D}(Y:Set D){g:D→V}(h:Measurable f)(p:∀ x,f x∈ Y)(v:Continuous (fun y:Y=>g y.val)): Measurable (fun i=>g (f i)):= v.measurable.comp ((by have hh: Measurable (fun i=> (⟨f i,p i⟩:Y)):=h.subtype_mk;exact hh))
lemma localMeas (H:Clearance p K k d)(G:BoxPay X o k c d): Measurable (fun x=>X (profile (K x))):= by
 let Y: Set (Pane N):={x|Guard x d}
 have ht: Continuous (fun x:Y=>X (profile x.val)):= G.cont.comp (Continuous.subtype_mk (profile_c.comp continuous_subtype_val) (fun x=> show profile x.val ∈ Openc (More N) d from ⟨x.val,x.property,by simpa using H.dept⟩))
 obtain ⟨_,_,_,P,_,_,_⟩:=H.glass
 exact mealGuard Y (g:=fun y=>X (profile y)) P.bill (H.onD) ht
lemma localColor (H:Clearance p K k d)(G:BoxPay X o k c d)(t:Seat N→SU.E)(x:Orbit N): X (profile (K (Lattice.gauge t x.1,threadG t x.2)))=twist (tradew N t) (X (profile (K x))):=by
 obtain ⟨_,_,_,P,_,_,_⟩:=H.glass
 rw [P.rev,Tulip.profile_g]
 exact G.color.frame t (doPort H x)

lemma fareSnap {S:Sa N}{x x' y y':Pane N}(u:Agrees S x x')(v:Agrees S y y'):
 fare S (profile x) (profile y)=fare S (profile x') (profile y'):=by
 refine sum_congr rfl fun i hi=>?_
 obtain ⟨p,g⟩:=(Finset.mem_filter.mp hi).2
 rw [show profile x i=profile x' i from ?_,show profile y i=profile y' i from ?_] <;> first|unfold profile;rw[u i p g]|unfold profile; rw[v i p g]
lemma fareNil {S:Sa N}{x y:Pane N}(p:Agrees S x y): fare S (profile x) (profile y)=0:= by
 rw [fareSnap p (show Agrees S y y from fun i _ _=>rfl)];simp [fare]

lemma box_pass (H:Clearance p K k d)(G:BoxPay X o k c d) {x:Pane N}(h:x∈setAwning p o){y:Pane N}(u:Agrees (roost k o) x y)(g:Guard y d) : bayonet K p o X x = X (profile y):=by
 rw [bayonet,Set.indicator_of_mem h]
 let w:Orbit N:=(x,Classical.arbitrary (Ids N))
 let W:Openc (More N) d:=⟨profile y,y,g,by simpa using H.dept⟩
 apply sub_eq_zero.mp; apply popping; refine (G.sees (doPort H w) W).trans_eq ?_
 have t:Agrees (roost k o) (K w) y:=fun i r s=> (H.light (x:=w) h i r s).trans (u i r s)
 change c*(fare _ (profile (K w)) (profile y)/_)=_
 rw [fareNil t,zero_div,mul_zero]

lemma bay_tick (H:Clearance p K k d)(G:BoxPay X o k c d) {x:Orbit N}(h:x.1∈setAwning p o):
 bayonet K p o X x.1=X (profile (K x)):= box_pass H G h (fun i p q=>(H.light (x:=x) h _ p q).symm) (H.onD x)
lemma bay_nil {x:Pane N}(h:x∉ setAwning p o): bayonet K p o X x=0:=Set.indicator_of_notMem h _
structure Awning (V : Pane N→ Op IΩ) (p:BudgetPoint)(o:Seat N)(k:ℕ)(c d:ℝ):Prop where
 meas: Measurable V
 shadeU (v):cork (V v)≤ c
 light(v:Pane N):sparHere (V v) (modesIn N (roost k o))
 shadeL {x y: Pane N}: x∈ setAwning p o→ y∈ setAwning p o→ cork (V x-V y)≤c*(fare (roost k o) (profile x) (profile y)/|d|)
 fence (x:Pane N): x∉ setAwning p o→V x=0
 fixed(g:Seat N→E)(x:Pane N): V (Lattice.gauge g x)=twist (tradew N g) (V x)
 dep: Lattice.LocalOn (roost (12+p.B) o) V

lemma setAwning_local {x y:Pane N}(g:Agrees (roost (12+p.B) o) x y):
 x∈setAwning p o ↔ y∈setAwning p o:= Chaff.fenceW (roost p.B o) (agrees_mono g (Finset.coe_subset.mpr ((Yaw.touchK _).trans (chainR (le_refl _))))) _
lemma saleAwning (H:Clearance p K k d)(G:BoxPay X o k c d): Awning (bayonet K p o X) p o k c d:=by
 let f:=bayonet K p o X
 let t:= Classical.arbitrary (Ids N)
 let j (x:Pane N):Orbit N:=(x,t)
 have be(x)(w:x∈setAwning p o): bayonet K p o X x= X (profile (K (j x))):=bay_tick H G (x:=j x) w
 have sees {x y : Pane N} (v:x ∈setAwning p o)(w:y ∈setAwning p o) :cork (f x-f y) ≤ c*(fare (roost k o) (profile x) (profile y)/ |d|):= by
   unfold f
   rw [be x v,be y w,← fareSnap (H.light (x:=j x) v) (H.light (x:=j y) w)]
   exact G.sees (doPort H (j x)) (doPort H (j y))
 refine ⟨((localMeas H G).comp (measurable_id.prodMk measurable_const)).indicator ping_o.measurableSet,?_,?_,sees,fun _ h=>bay_nil h,?_,?_⟩
 · intro v;by_cases h:v∈setAwning p o
   ·rw [be v h]; exact G.award (doPort H (j v))
   rw [bay_nil h]; simp only [cork,Matrix.zero_apply,norm_zero,sum_const_zero]

   exact (show 0≤cork (X (profile (K (j v)))) from by unfold cork;positivity).trans (G.award (doPort H (j v)))
 · intro v;by_cases h:v∈setAwning p o
   · rw[be v h]; exact G.modes (doPort H (j v))
   rw [bay_nil h];exact spar0 _
 · intro g x; let y:Orbit N:=(Lattice.gauge g x,threadG g t)
   by_cases h:x∈setAwning p o
   · rw [bay_tick H G (x:=y) ((pingB x g).mpr h),be _ h];exact localColor H G g (j x)
   rw [bay_nil (p:=p) (o:=o) (mt (pingB x g).mp h), bay_nil h,map_zero]
 intro x y t
 have r:=setAwning_local (p:=p) t
 by_cases v:x∈setAwning p o
 · apply sub_eq_zero.mp;apply popping;refine (sees v (r.mp v)).trans_eq ?_
   rw [fareNil (agrees_mono t (Finset.coe_subset.mpr (roost_expand (H.priceLen.trans (Nat.le_add_left _ _))))),zero_div,mul_zero]
 rw [bay_nil v,bay_nil (mt r.mpr v)]

end YM.CF.Bay
