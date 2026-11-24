import Lucent.Op
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment
set_option quotPrecheck false

open Peaks Scree Mir Buffered.Afterglow
open Lattice
open RG
variable (N:Side)(s:ℤ)
local notation:max "pl" s:max => plane 3 s
local notation:max "mₛ" s:max => (pl s).motion
local notation:max "fₛ" s:max => (pl s).flee
local notation:max "t₃" s:max N:max => theta (carR 3 s N)

def sash (s:ℤ)(W:Staff):Staff:=⟨mₛ s W.hub,fₛ s W.u,(mₛ s W.face.1,W.face.2),W.spin.swap,W.steps.map (fun x=>x.rotate (Signed.mirror 3)),by rw [show nodeC _=_ from ((pl s).mote W.u).symm]; exact (mirror_travel (pl s) W.xo W.steps).trans (congrArg (pl s).motion W.stop_at)⟩
local notation:max "sa" => Signed.mirror 3
variable (W:Staff)
def day (D:PlaqAxes) := D.val.1≠3∧D.val.2≠3
lemma day_steps (D:PlaqAxes)(h:day D): ((Lattice.square D.val.1 D.val.2).map fun x=>x.rotate sa)= Lattice.square D.val.1 D.val.2:=by
 obtain ⟨a,b⟩:=h; simp [Signed.mirror,Step.rotate,posDir,negDir,Lattice.square,Ne.symm a,Ne.symm b]

lemma motionVis (x:Cover)(L:Walk) : visits (mₛ s x) (L.map fun d=>d.rotate sa)= (visits x L).map (mₛ s) := by
 induction L generalizing x with
 | nil=>rfl
 | cons d L ih=>
   rw [visits,List.map_cons,List.map_cons,visits,Step.vec_rotate,← show _ = mₛ s x + (sa).act d.vec from (pl s).motion_v x _, ih] -- motion_v?
lemma motionDeck (x:Cover) {r}(y:Cover)(h:y∈skyDeck x r) : mₛ s y ∈ skyDeck (mₛ s x) r:= by
 obtain ⟨k,q,rfl⟩:=mem_image.mp h
 rw [add_comm k,Shape.motion_v]; apply mem_image.mpr; refine ⟨(sa).act k,?_,add_comm ..⟩
 rw [box_test]; obtain ⟨d,e⟩:=box_test.mp q; constructor <;> intro i <;> specialize d i <;> specialize e i <;> simp [Signed.mirror,Signed.act] <;> split_ifs <;> omega -- no

lemma sash_pay {r w}(h:W.Pays r w)(d:day W.face.2): (sash s W).Pays r w:=by
 constructor
 · exact (List.length_map ..).le.trans h.stepCost
 · intro y v; rw [show (sash s W).xo=mₛ s W.xo from ((pl s).mote W.u).symm,show visits _ (sash s W).steps=_ from motionVis s W.xo W.steps] at v -- mote not defeq
   obtain ⟨k,q,rfl⟩:=List.mem_map.mp v; exact motionDeck s _ _ (h.roomSites k q)
 · intro y v
   let g:=Lattice.square W.face.2.val.1 W.face.2.val.2
   change y∈(visits (mₛ s W.face.1) g).toFinset at v
   rw [←show g.map _=g from day_steps _ d, motionVis] at v
   obtain ⟨k,q,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp v); exact motionDeck s _ _ (h.faceSites (List.mem_toFinset.mpr q))
private lemma tolerance(X:Support (More N))(V:Pane N)(t:ℝ) : pingS t X V ↔ ∃ e, e<t ∧ Healthy e X V:=by
  classical
  constructor; swap; · rintro ⟨e,v,q⟩; exact ping_lo v q
  intro p; let S:=univ.filter fun i:Face (Per (More N))=> ¬Disjoint X (touched i); let k(i:Face (Per (More N))):= SU.group.chord (faceValue V i)
  have he : ∃ e, e<t ∧ ∀ i∈S, k i<e:=by
    by_cases h:S.Nonempty; swap; · exact ⟨t-1,by linarith,fun i u=>(h ⟨i,u⟩).elim⟩
    obtain ⟨b,u,hb⟩:= exists_between ((sup'_lt_iff ..).mpr (fun i e=> p i (mem_filter.mp e).2) : S.sup' h k<t)
    exact ⟨b,hb,fun i e=> lt_of_le_of_lt (le_sup' k e) u⟩
  obtain ⟨b,g,hq⟩:=he; exact ⟨b,g, ping_le (fun i e=>hq i (mem_filter.mpr ⟨mem_univ _,e⟩))⟩

lemma sash_ping (X:Support (More N)) (U:Pane N)(t:ℝ) : pingS t X (fling 3 s N U) ↔ pingS t (X.image ((pl s).anon N)) U:=by
 rw [tolerance N,tolerance N,fling_eq]; refine exists_congr fun i=> and_congr_right fun _=> WardBin.Wheels.safe _ _ _|>.symm
lemma sash_gate (r:ℕ) : (sash s W).gateS r N=(W.gateS r N).image ((pl s).anon N):=by
 unfold Staff.gateS; rw [←wrap_pav,←wrap_pav,image_image]

 have inv (x:Cover): mₛ s (mₛ s x)=x:=by funext i; simp [fling_move]; split_ifs <;> ring
 ext i; constructor
 · rintro h; obtain ⟨x,k,rfl⟩:=mem_image.mp h; have e:=motionDeck s _ _ (show x∈skyDeck (mₛ s W.hub) r from k); rw [inv] at e; exact mem_image.mpr ⟨_,e,((pl s).anno _).trans (congrArg _ (inv x))⟩ 
 rintro h; obtain ⟨x,k,rfl⟩:=mem_image.mp h; exact mem_image.mpr ⟨_,motionDeck s _ _ k,((pl s).anno x).symm⟩

#check @wrap_pav
#check @halo_spec

lemma pearl_reflect (ρ t:ℝ)(r:ℕ)(x:Pane N)(d:day W.face.2): W.pearl ρ N r t (fling 3 s N x)=(sash s W).pearl ρ N r t x:=by
 unfold Staff.pearl; rw [sash_ping,sash_gate]; split; swap; rfl
 unfold Staff.edgeBudget; rw [fling_eq,travel_pull]
 unfold faceValue; rw [travel_pull, day_steps _ d]

 let a:=(pl s).anon N
 have h:a (W.scope N)= (sash s W).scope N := ((pl s).anno W.xo).trans (congrArg _ ((pl s).mote W.u))
 change SU.group.adjoint (travel x (a _) _) (ρ • SU.group.curvature (travel x (a (wrap _ _)) _))=_
 rw [h, show a (wrap (More N) W.face.1)=_ from (pl s).anno _]
 try rfl

set_option maxHeartbeats 800000 in
lemma pin_c (a: Fin 2) (j:SpinIdx) : pin 3 j (upSpin a)=(if j=dnSpin a then 1 else 0) ∧ pin 3 j (dnSpin a)=(if j=upSpin a then -1 else 0):= by
 have g :gammaOp 3= !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]:=rfl
 fin_cases a <;> fin_cases j <;> norm_num [pin, g,upSpin,dnSpin, grading, SpinIdx,Matrix.mul_apply, Fin.sum_univ_succ] <;> exact ⟨rfl,rfl⟩

lemma cellSwap (u:Cover)(b:Twah.DirSpin)(i j:SU.Slot):
 t₃ s N (cell N u b i j)=cell N (fₛ s u) b.swap j i:= by
 unfold cell
 rw [theta_mul,(flips_basisC 3 s N u _ i).1,(flips_basisC 3 s N u _ j).2]
 simp_rw [(pin_c _ _).1,(pin_c _ _).2,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,one_smul,neg_one_smul]
 rw [map_neg,smul_neg, mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,SitSpin.cr_swap, neg_neg]
 try rfl

#check @theta_twist_right
#check @Lifted.gaugeSquare
-- show flips preserve Singing. via AtSupport true
#print AtSupport

