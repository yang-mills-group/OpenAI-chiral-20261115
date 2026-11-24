import Bay.Porch
import YM.CF.Proa.Uta
import YM.CF.Thera.Jolt
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section

open scoped Matrix.Norms.Frobenius ContDiff in
lemma YM.CF.Bay.fund_jet (i j:YM.CF.SU.F): ContDiff ℝ ω (fun x:YM.CF.SU.group.Color=>YM.CF.SU.fund (YM.CF.SU.group.lieExp x) i j):=((YM.CF.Laic.entry_F i j).contDiff.comp YM.CF.SU.group.exp_jet)
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff

variable {N:Side}{d:ℝ}
abbrev Lag(N:Side) := fieldDir SU.group (More N) 1
abbrev Øc:= SU.group.Color
def flower(x:Lag N):= profile (represent x)

abbrev fire(x:Øc): Op SU.F := SU.fund (SU.group.lieExp x)
lemma fire_paid : ContDiff ℝ ω fire:=by
  apply contDiff_iff_contDiffAt.mpr
  intro x; apply tort.mpr; exact fun i j=> (fund_jet i j).contDiffAt
lemma flora(k:ℕ) : ∃ p:ℝ,0≤p ∧ ∀ (N:Side) (x:Lag N),‖x‖ ≤ 1 → Allows k flower x p:=by
 obtain ⟨p,h,H⟩ := compact_allow k zero_le_one fire (fire_paid.of_le le_top)
 let K:= composeCost k p 1
 have hp:0≤K:=by unfold K composeCost; positivity
 obtain ⟨a,g,q⟩:= Proa.profile_X k K hp
 refine ⟨a,g,fun N x hx=>q _ x fun i=>?_⟩
 let V : Lag N→L[ℝ] Øc := ContinuousLinearMap.proj (YM.Extra.Iteration.Channel.bondBody _ i)
 have he(y:Lag N) : ‖V y‖≤ ‖y‖:= norm_le_pi_norm y _
 have ht:Allows k V x 1:= allows_linear (V.opNorm_le_bound zero_le_one fun y=> (he y).trans_eq (one_mul _).symm) ((he x).trans hx)
 rw [show (fun t:Lag N=> SU.fund (represent t i))= fire ∘ V from ?_]
 · exact (H (V x) ((he x).trans hx)).comp ht
 funext x; rw[Work.F03.represent_link];rfl


lemma atSepal(p:0<d) : ∃ ρ:ℝ,0<ρ ∧ ρ ≤ 1 ∧ ∀ (N:Side)(x:Lag N),‖x‖ ≤ ρ → ball (flower x) (d/2) ⊆ Openc (More N) d :=by
 let f(z:Øc) := brand (SU.group.lieExp z)
 have h:Continuous f:= Dial.spinD.comp (f:=SU.group.lieExp) ((SU.fund_cont.isClosedEmbedding group.mat_injective).isEmbedding.continuous_iff.mpr fire_paid.continuous)
 obtain ⟨t,ht,hh⟩:=Metric.continuousAt_iff.mp (show ContinuousAt f 0 from h.continuousAt) (d/2) (half_pos p)
 let r:=min (t/2) 1
 refine ⟨r,lt_min (half_pos ht) (by norm_num),min_le_right ..,fun N x g z k=>?_⟩
 have hg: ‖flower x-1‖ ≤ d/2:=by
   apply (pi_norm_le_iff_of_nonneg (half_pos p).le).mpr fun i=> (pi_norm_le_iff_of_nonneg (half_pos p).le).mpr fun b=>?_
   let y:= x (YM.Extra.Iteration.Channel.bondBody (More N) i)
   have hv: dist y 0 <t:= by rw [dist_zero_right];exact (le_trans (norm_le_pi_norm x _) (g.trans (min_le_left ..))).trans_lt (half_lt_self ht)
   have he:f 0=1:= by simp [f,brand_one]
   have l:=hh hv; rw[he,dist_eq_norm] at l

   cases b
   · change ‖star (brand (represent x i))- (1:Twig)‖ ≤ _
     rw[←star_one (R:=Twig),←star_sub,norm_star,Work.F03.represent_link];exact l.le
   · change ‖brand (represent x i)- (1:Twig)‖ ≤ _
     rw[Work.F03.represent_link];exact l.le
 rw [mem_ball_iff_norm] at k
 refine ⟨1,guard0 p.le,?_⟩; rw [profile_trivial]
 exact (norm_sub_le_norm_sub_add_norm_sub z (flower x) 1).trans_lt ((add_lt_add_of_lt_of_le k hg).trans_eq (add_halves ..))

abbrev GateR(N:Side)(d:ℝ):=Openc (More N) d
abbrev Plank (N:Side)(d:ℝ):= Raw (↥(GateR N d)) (Single N)
abbrev Essay {N:Side} {d:ℝ}(s:Sa N)(c:Toll (Single N)) : Plank N d → Prop :=
 Suite (badge _) (bail N d) (bail N d) s c
def pic{d:ℝ}(F: Plank N d) (x:GateR N d):= Matrix.trace (F x)
def picP{d:ℝ}(F: Plank N d) (W:Pane N):ℂ:= equalizer (pic F) (profile W)
def picL{d:ℝ}(F: Plank N d) : Lag N→ℂ:= picP F ∘ represent

variable {F F':Plank N d}{S:Sa N}{C:Toll (Single N)}
lemma in_pic {x:GateR N d} : equalizer (pic F) x.val=pic F x:=dif_pos x.property
lemma essay_looks(q:Essay S C F) : Looks _ (pic F) ∧ Continuous (pic F) ∧
     ∀ i,‖pic F i‖≤ ledgerV C:=by
 have h(i):pic F i=∑ a:Single N,F i a a:=rfl
 rw[funext h]
 refine ⟨fun T g u w=> ?_,continuous_finsetSum _ (fun i _=> (q.expo i i).connected),fun i=>?_⟩

 · have hh(i:Single N): Looks _ (fun x=>F x i i):=q.fuel i i
   unfold Function.comp
   convert (DifferentiableOn.sum (𝕜:=ℂ) (s:=T) (u:=univ) (A:=fun i x=>F (u x) i i) (fun i _=> hh i _ g _ w)) using 1 <;> try rfl
   funext x
   rw [Finset.sum_apply]
 exact (norm_sum_le ..).trans (sum_le_sum fun a _=> ((q.expo a a).bounded _).trans (single_le_sum (fun b _=>q.nonn a b) (mem_univ _)))

lemma pic_gauge(q:Essay S C F)(g:Site (More N)→E)(U:Pane N):
    picP F (Lattice.gauge g U)=picP F U:=by
 unfold picP
 rw [profile_g]
 let Y:=tradew N g
 by_cases he:profile U∈GateR N d
 · let x:GateR N d:= ⟨_,he⟩; let z:GateR N d:= ⟨_,o_act g x.val _ he⟩
   have hg:F z = ((Y.val)*F x)*(star Y.val):=by
      have hu:= q.frame g x
      change F z * Y.val = _ at hu
      exact ((mul_one _).symm.trans (((congrArg (fun u=>F z*u) Y.property.2).symm.trans ((mul_assoc ..).symm.trans (congrArg (fun w=>w*_) hu))))) 
   change equalizer _ z.val=equalizer _ x.val
   rw[in_pic,in_pic,pic,hg]
   rw[Matrix.trace_mul_cycle,Y.property.1, one_mul]; rfl
 have h' : relayg g (profile U)∉GateR N d:=by
   intro v; apply he
   have hp:=o_act g⁻¹ _ d v
   rw [←profile_g,←profile_g] at hp
   convert hp using 2
   funext i; unfold Lattice.gauge; simp;group
 rw[Jet.equalizer,dif_neg h',Jet.equalizer,dif_neg he]

lemma pic_grad (q:Essay S C F)
    (hx:DifferentiableAt ℝ (picL F) 0): fderiv ℝ (picL F) 0 = 0:=by
 let A:=picL F; let p:= fderiv ℝ A 0
 let K(g:E):Lag N →L[ℝ] Lag N:= ContinuousLinearMap.pi (fun i => (group.adjoint g).toContinuousLinearMap ∘L (ContinuousLinearMap.proj i))
 have he(g:E): A ∘ K g = A:=by
    funext x; change picP _ (represent _)=_
    rw[show represent (K g x) = Lattice.gauge (fun _=>g) (represent x) from ?_,pic_gauge q]; rfl
    funext j;rw[Lattice.gauge,Work.F03.represent_link,Work.F03.represent_link]; exact Next.SectorChange.exp_adjoint ..
 have hh(g:E): p.comp (K g)=p:=by
   have hz:= ((show DifferentiableAt ℝ A (K g 0) from by rw[map_zero];exact hx).hasFDerivAt.comp _ (K g).hasFDerivAt).fderiv
   rw[map_zero, he] at hz
   exact hz.symm

 have hp'(e: Edge (Site (More N))):p.comp (Nacre.put group (More N) e)=0:=by
   let f:= (p.comp (Nacre.put group _ e)).toLinearMap
   have ht(g:E)(u:Øc): K g (Nacre.put group _ e u)= Nacre.put group _ e (group.adjoint g u):=by
      funext i; change group.adjoint g (Pi.single (M:=fun _=>Øc) (Nacre.Trot _ e) u i)= Pi.single (M:=fun _=>Øc) (Nacre.Trot _ e) (group.adjoint g u) i
      by_cases h:i=Nacre.Trot _ e <;> simp [h]
   have hz:f=0:=StressFlux.linear_invariant Thera.yet_one f
      (fun g u=> by change p (Nacre.put group _ e _)=_; rw[← ht];exact DFunLike.congr_fun (hh g) _)
   exact ContinuousLinearMap.ext fun i=> DFunLike.congr_fun hz i
 exact ContinuousLinearMap.ext (fun u=>by
   change p u = 0
   nth_rw 1 [Nacre.put_sum u,map_sum]
   exact sum_eq_zero fun i _=> DFunLike.congr_fun (hp' i) _)

/-- cap on plank chart independent of torus, multiplies ledger. -/
structure Twine (k:ℕ)(d D r:ℝ): Prop where
 dr:0<d
 dp:0<D
 rp:0<r
 pay {N:Side}(F:Plank N d){C:Toll (Single N)}{S:Sa N}(q:Essay S C F)(x:Lag N):
   ‖x‖≤r→ Allows k (picL F) x (D*ledgerV C) ∧ flower x ∈ GateR N d
lemma twining (k:ℕ)(p:0<d):∃ D r,Twine k d D r:=by
 obtain ⟨r,t,x,H⟩:=atSepal p
 obtain ⟨V,b,f⟩:=flora k
 let u:=d/2; have he:0<u:=half_pos p
 let L:=(1+2^k/u)^k
 refine ⟨composeCost k L V,r,⟨p,by unfold composeCost L; positivity,t,?_⟩⟩
 intro N F C S q y h
 have ht:=H N y h
 refine ⟨?_,ht (mem_ball_self he)⟩
 obtain ⟨j,l,a⟩:=essay_looks q
 have hy:=Jet.allows_looks j l ht he k a
 change Allows k ((equalizer (pic F)) ∘ flower) _ _
 exact ((hy.comp (f N y (h.trans x))).mono (le_of_eq (by unfold composeCost L u; ring)))

end D
end YM.CF.Bay
#print axioms YM.CF.Bay.D.twining
