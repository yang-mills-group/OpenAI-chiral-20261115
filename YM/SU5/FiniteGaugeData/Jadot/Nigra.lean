import YM.SU5.FiniteGaugeData.Jadot.Gato
/-! # WP23: horizon and column appointments. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Window.Presidio
open Parcel.Tanin Fock Fock.Reduction Reduction.Hutch Reduction.Drama Reduction.Drama.Pack Reduction.Jersey -- tune resolution
open Reduction.Dinar Reduction.Rheims Reduction.Verna Reduction.Dijon
open Next.Free Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision Tree Finset Exterior
open Lat Rush Cube Scroll SU Peaks Dial Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Cour Fir Ember Aroma Cascade Gall
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
open Pivot Fock.Brique Menton Gato
attribute [local instance] opCStarAlgebra
namespace Nigra
variable {N:Side}{j k l u v:ℕ}{a b c r t s μ ν ε δ:ℝ}{P Q M D X W:Op (Single N)} (p:1≤j){D₀:Tulip.Male}
-- #check Menton.fixp
-- #check @tenderN
-- #check @FixB
/- define Wantion L.Z book, dial issue from one support. w fixed. -/
abbrev warpB(j:ℕ)(p:1≤j):= max (FixN j p) ((Gato.tender_set p).choose)
abbrev CaperB(j:ℕ)(p:1≤j):= Real.sqrt ((annual p).choose)
abbrev nnCost(s:ℝ):=(Real.sqrt s)⁻¹ +1
structure Cream(P Q:Op (Single N))(c s kL kZ:ℝ)(w z:ℕ)(M D:Op (Single N)):Prop where
 lens: Neighbor w M
 grove: Neighbor z D
 zero : ∃ u:ℝ, Currency Q P 0 kL kZ u c M D
 full (μ:ℝ)(p:0<μ)(t:μ≤ s): Currency Q P μ kL kZ (nnCost μ) c M D -- s last f.C
-- require Liquidity w at s tiny NOT automatically? from cap? remove. also parameter b.
-- kitchen. choose mask tolerance (εL)
def cashK (b a:ℝ):ℝ:= Real.sqrt ((Real.sqrt b)*a)
lemma small (a:ℝ)(e:0<ε):∀ᶠ t:ℝ in 𝓝 0,cashK t a ≤ ε:=by
 let f(x:ℝ):= cashK x a; have hf: ContinuousAt f 0:=by unfold f cashK; fun_prop
 exact hf.tendsto.eventually (ge_mem_nhds (show f 0 < ε from by simpa [f,cashK] using e)) -- gt vs ge orientation check name
lemma buy_r (a:ℝ)(e:0<ε)(u:0<s):∃ t:ℝ,0<t∧ t≤ s∧ cashK t a ≤ ε :=by
 have hx:= ((small a e).and (ge_mem_nhds u)).filter_mono (show nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 0 from nhdsWithin_le_nhds)
 obtain ⟨t,⟨h,v⟩,z⟩:= (hx.and self_mem_nhdsWithin).exists; exact ⟨t,z,v,h⟩
private lemma capCharge (p:0<μ)(q:μ≤1)(v:IsStarProjection Q): ‖Lumi Q P μ‖≤ (Real.sqrt μ)⁻¹:= tangle_power v p q (Q*P)
structure StageL(P Q:Op (Single N))(a c s:ℝ)(k:ℕ)(M:Op (Single N)): Prop where
 live:IsSelfAdjoint M
 site:M*(1-Q)=1-Q
 border:Neighbor k M
 lattice(μ:ℝ)(e:0≤μ)(g:μ≤ s): cellU univ (M-Lumi Q P μ) a ∧ ∃ K:Op (Single N),IsSelfAdjoint K∧ K≤Lumi Q P μ ∧ Canon (Single N) (1/2) ≤ K ∧ ‖M-K‖≤1/8
 cost(μ:ℝ)(p:0<μ)(t:μ≤ s): ‖M‖≤ nnCost μ
structure StageZ(P Q:Op (Single N))(a c s:ℝ)(k:ℕ)(D:Op (Single N)):Prop where
 site:Spear Q D
 border:Neighbor k D
 terrace(μ:ℝ)(e:0≤μ)(g:μ≤ s): cellU univ (D-Zami Q P μ) a∧cellU univ (star (D-Zami Q P μ)) a
 cost: ‖D‖≤2
local notation "Q_"=> tickA N
-- Issue I. Steps K.P
lemma Zissue (H:Booster (tickA N) P W c)(u:0<s)(v:s≤1)(t:cashK s c ≤ a/2)(ℓ:a≤1)(e:Liquid k (Zami Q_ P s) (a/2)):∃ D,StageZ P Q_ a c s k D:=by
 let A:=Zami Q_ P s; obtain ⟨D,z,r,p⟩:= pinchZ (Rheims.heart H.base (H.te u.le)) e
 refine ⟨D,z,p,fun x hx hk=> ?_, (le_trans ?_ (show a/2+1≤2 from by linarith))⟩
 · let B:=Zami Q_ P x; let T:=D-A; let U:=B-A; obtain ⟨-,y,q⟩:=H.Change hx hk; have ht:cellU univ T (a/2):= cellU.of_norm r; have hv:cellU univ (star T) (a/2):= cellU.of_norm ((norm_star _).trans_le r); rw [show D-Zami Q_ P x=T-U by unfold T U A B; abel,star_sub]; exact ⟨cellU.mono (cellU.offset_cost ht (cellU.mono y t)) (le_of_eq (by ring)), cellU.mono (cellU.offset_cost hv (cellU.mono q t)) (le_of_eq (by ring))⟩
 · nth_rw 1 [←sub_add_cancel D A]; exact (norm_add_le ..).trans (add_le_add r (revenueZZ H.base (H.te u.le) u.le))
lemma Lissue (H:Booster Q_ P W c)(u:0<s)(v:s≤1)(t:cashK s c ≤ a/2)(e:Liquid l (Lumi Q_ P s) (min (a/2) (1/8))):∃ M,StageL P Q_ a c s l M:=by
 let A:= Lumi Q_ P s; obtain ⟨M,h,w,x,y⟩:= pinchL (pole H.base (H.te u.le)) e; have k : ‖M-A‖≤1/8:= x.trans (min_le_right ..); have he:= cellU.of_norm (L:=univ) (x.trans (min_le_left ..)) -- need S
 refine ⟨M,h,w,y,fun μ e f=>?_,fun μ e f=>?_⟩
 · let B:= Lumi Q_ P μ; let T:=M-A; let U:= B-A
   refine ⟨by rw [show M-Lumi Q_ P μ = T-U by unfold T U A B; abel]; exact cellU.mono (cellU.offset_cost he (cellU.mono (H.Change e f).1 t)) (le_of_eq (by ring)), A, (pole H.base (H.te u.le)).litA.isSelfAdjoint, sub_nonneg.mp (lumi_diff H.base (H.te e) f (H.te u.le)).1, lumi_floor H.base H.iceE u.le v (H.te u.le), k⟩
 · nth_rw 1 [← sub_add_cancel M A]; unfold nnCost; exact (norm_add_le ..).trans (by refine le_trans (add_le_add k (capCharge u v H.base)) ?_; have hz:= inv_anti₀ (Real.sqrt_pos.mpr e) (Real.sqrt_le_sqrt f); linarith only [hz]) -- tune local A defeq
lemma Cream.issue (h:Booster Q P W c)(g:StageL P Q a c s l M)(v:StageZ P Q b c μ u D)(p:t≤ s)(k:t≤μ)(w:t≤1)(h0:0≤t)(l0:0≤a)(w0:a≤1)(l1:0≤b)(w1:b≤1): Cream P Q (Real.sqrt c) t a b l u M D:=by
 have he (x:ℝ)(o:ℝ)(e:0≤x)(l:x≤t)(j: ‖Lumi Q P x‖≤o)(F:‖M‖≤o): Currency Q P x a b o (Real.sqrt c) M D:=by
    obtain ⟨Y,u⟩:=g.lattice x e (l.trans p); obtain ⟨H,H'⟩:= v.terrace x e (l.trans k); exact ⟨h.base,h.iceE,h.te e,e,l.trans w,j,h.visits e,F,l0,w0,l1,w1,g.live,g.site,Y,v.site,v.cost,H,H',u⟩
 refine ⟨g.border,v.border,⟨max ‖Lumi Q P 0‖ ‖M‖,he 0 _ le_rfl h0 (le_max_left ..) (le_max_right ..)⟩,fun x p' g' => he x _ p'.le g' ((capCharge p' (g'.trans w) h.base).trans (le_add_of_nonneg_right zero_le_one)) (g.cost _ p' (g'.trans p))⟩
-- issue statement ∃ traversals: order on widths first. Note after wantL installed, choose Z relative ANY ask. issue paid at t pre cap.Clock. Later must choose true μ via pageable.S.
include p
lemma bank(p':0<ε)(e: ε≤1): ∃ wL:ℕ,∀ (b:ℝ),0<b→ b≤1→∃ (wB:ℕ)(t:ℝ),0<t∧ t≤1∧∀ (N:Side),warpB j p≤ N.val→Even N.val→∀ M:Tulip.Male, let R:= spar j M (1:Bkg (More N)); IsStarProjection R → ∃ X Y:Op (Single N), Cream R (tickA N) (CaperB j p) t ε b wL wB X Y:=by
 let c:= (annual p).choose; obtain ⟨u,l,L,T⟩:=buy_r c (half_pos p') zero_lt_one; have H1:= (tender_set p).choose_spec; obtain ⟨r,Q⟩:= H1 u (min (ε/2) (1/8)) l L (lt_min (half_pos p') (by norm_num)); refine ⟨r,fun b b0 U=>?_⟩
 obtain ⟨v,sj,e',s'⟩:= buy_r c (half_pos b0) l; obtain ⟨z,P⟩:= H1 v (b/2) sj (e'.trans L) (half_pos b0)
 refine ⟨z,v,sj,e'.trans L,?_⟩; intro N α y M S X
 have hT: (tender_set p).choose≤ N.val:=le_trans (le_max_right ..) α; obtain ⟨W,t⟩:= fixe p ((le_max_left ..).trans α) y X; obtain ⟨M_,Mh⟩:= Lissue t l L T (Q N hT M X).1; obtain ⟨D,Eh⟩:= Zissue t sj (e'.trans L) s' U (P N hT M X).2; exact ⟨M_,D,Cream.issue t Mh Eh e' le_rfl (e'.trans L) sj.le p'.le e b0.le U⟩ -- let Symbol.R
end Nigra
end YM.CF.Window.Presidio
