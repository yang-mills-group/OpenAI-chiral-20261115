import YM.SU5.FiniteGaugeData.Nine.Strand
import YM.CF.Levier.Vase
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Window.Pivot
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
variable {N:Side}(o:Cover)
open Brique Mir Phase RP Largo Spire Reflect
local notation "Μ"=> Single N
open Fock.Brique Lifted Girt
open Buffered.Afterglow.Hierarchy
variable {W:Pane N→ℂ}{T R U:Support (More N)}
local notation "Z"=> (polarQ o)
open Levier
lemma sky_twice (x:Pane N): Yg (polarQ o) (Yg (polarQ o) x)=x:=by rw [←kor,polar_id,Nacre.blank]
lemma sky_fare (x:Pane N): Tulip.fare U (profile (Yg (polarQ o) x)) 1=Tulip.fare (U.image ((Z).anon N)) (profile x) 1:=by -- notation
 have he:profile (Yg (polarQ o) x)= gateC false (polarQ o) (profile x):= veil_p ..; have hv: gateC false (polarQ o) (1:Chin N)=1:=by funext i k; rfl
 rw [he]; nth_rw 1 [←hv]; exact roseC ..
structure Earn(o:Cover)(S:Support (More N)) : Prop where
 symm: S.image ((polarQ o).anon N)=S
lemma Earn.ann (g:Earn o T)(x:Seat N)(p:x∈T):(Z).anon N x∈T:=g.symm ▸ mem_image_of_mem ((Z).anon N) p
lemma pole_center(x:Cover): (polarQ x).motion x=x:=funext fun i=>by rw [palm_vis]; split<;> omega
lemma sky_center : (polarQ o).anon N (wrap (More N) o)=wrap (More N) o:= by rw [Shape.anno,pole_center]
variable (F:Corset T R (wrap (More N) o))(gR:Earn o R)(gT: Earn o T)
local notation "Y"=> (Yg (polarQ o))
def frameP:Corset T R (wrap (More N) o) where
 g x:= F.g (Y x) ∘ (Z).anon N
 up_cont:= continuous_pi fun i=> ((continuous_apply _).comp F.up_cont).comp (Wilson.continuous_pull ..)
 locale i h:=fun x y p=> F.locale _ (Earn.ann o gT _ h) _ _ (Yg_agrees _ _ (by rw [gR.symm]; exact p))
 law g x:=by rw [van,F.law]; funext i; simp only [Function.comp,Pi.mul_apply,Pi.inv_apply,globalH]; rw [sky_center,anon_sky]
local notation "K"=> (frameP o F gR gT)
lemma sky_cargo (W:Pane N→ℂ)(A:FC (Single N)): pageF o N (cargo F W A)=cargo K (W∘Y) (imageQ Z N A):=by
 funext i; unfold pageF castT cargo; change twist (quantU _) (W (Y i.1) • _)=_; rw [twist_scalar]; refine congrArg (fun a: FC (Single N)=> W (Y i.1) • a) ?_; exact pollen ..
-- Cash.
def sapW (W:Pane N→ℂ): Pane N→ℂ:= W * (W∘Y)
lemma sky_identity : (sapW o W)∘Y=sapW o W:=by funext i; unfold sapW; simp only [Function.comp, Pi.mul_apply, sky_twice]; exact mul_comm ..
local notation "b"=> (sapW o W)
include gR
lemma issue_Ψ (p:Stump R W): Stump R (sapW o W):= by
 unfold sapW; refine ⟨p.cont.mul (p.cont.comp (Wilson.continuous_pull ..)),fun x y u=> congrArg₂ (·*·) (p.zone x y u) (p.zone _ _ (Yg_agrees _ _ ?_)),fun i=>?_,fun g i=> ?_⟩; · rw [gR.symm]; exact u
 · rw [Pi.mul_apply,norm_mul, Function.comp_apply]; exact (mul_le_of_le_one_left (norm_nonneg _) (p.unitB _)).trans (p.unitB _)
 simp only [Pi.mul_apply, Function.comp_apply,van]; exact congrArg₂ (·*·) (p.vision ..) (p.vision ..)
omit gR
variable {ε:ℝ}{L: Loom N}
include gR
lemma cutBoth (gU: Earn o U)(p:CashMask F W U ε L): CashMask F (sapW o W) U ε L ∧ CashMask (frameP o F gR gT) (sapW o W) U ε L:=by
 let K':=K; have hv:CashMask F b U ε L:= ⟨issue_Ψ o gR p.faces,fun i h=> p.top _ (left_ne_zero_of_mul h), fun i h=> p.lamp _ (left_ne_zero_of_mul h)⟩
 refine ⟨hv,hv.faces,fun i h=>?_,hv.lamp⟩; have he:= p.top (Y i) (right_ne_zero_of_mul h); have hz: gauge ((K).g i) i = Y (gauge (F.g (Y i)) (Y i)):=by rw [van,sky_twice]; rfl
 rw [hz,sky_fare,gU.symm]; exact he
end YM.CF.Window.Pivot
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
variable (o:Cover) {N:Side}(A: Finset (Face ℤ))(t:ℝ)
open Window.Pivot
-- name conflict `scape`
open Nacre
#check Quest.scape
local notation "Z"=> (polarQ o)
abbrev jumpsC (a:Axis):= moveC a (o a)
def leaps(L:LinksC):= jumpsC o 0 (jumpsC o 1 (jumpsC o 2 L))
lemma leaps_cont : Continuous (leaps o):=(move_cont ..).comp ((move_cont ..).comp (move_cont ..))
lemma leaps_here(x:Pane N):onC N (Yg (polarQ o) x)= leaps o (onC N x):=by rw [polarQ,Nacre.kor,Nacre.kor]; change onC _ (fling 0 _ _ (fling 1 _ _ (fling 2 _ _ x)))=_; unfold leaps jumpsC; simp only [reflect_onC]
variable (S:Finset Cover)
lemma jumps_cover (r:ℕ): πS o (Quest.scape o r)=Quest.scape o r:=by
 have he(x:Cover)(u:x∈Quest.scape o r) : (polarQ o).motion x∈Quest.scape o r:=by
    refine sap_box.mpr fun j=> ?_; have h:=sap_box.mp u j; rw [palm_vis]; split<;> omega
 ext x; refine ⟨fun h=>?_,fun h=>mem_image.mpr ⟨_,he x h,(by rw [←palm,polar_id]; simp [Shape.motion,incX])⟩⟩; obtain ⟨z,w,rfl⟩:=mem_image.mp h; exact he z w


lemma leaps_earn (r:ℕ): Earn o (region (Quest.scape o r) N):=by
 constructor; unfold region; rw [image_image]; let f:= wrap (More N); rw [show (Z).anon N ∘ (f)= _ from (funext fun i=>Shape.anno (polarQ o) i : (Z).anon N ∘ (⇑f)= (⇑f) ∘ ((Z).motion)), ←image_image,show (Quest.scape o r).image ((Z).motion)=_ from jumps_cover o r]
lemma leaps_agree {X Y:LinksC}{S:Finset Cover} (p:Agrees (πS o S) X Y): Agrees S (leaps o X) (leaps o Y):=by
 -- orientation inner moves? `Agrees S(move0 (move1 ...))`, need `p` reflected via mirror2 mirror1 mirror0 of S. equals ΠS by natural. π_party order opposite. def ΠS=polarQ order2.1.0. rfl.
 have h: refract 2 (o 2) (refract 1 (o 1) (refract 0 (o 0) S))=πS o S:=by unfold refract πS; rw [image_image,image_image]; apply congrArg (fun a=> image a S); funext x; rw [polarQ,palm,palm]; rfl
 rw [← h] at p; exact moved_agree _ _ (moved_agree _ _ (moved_agree _ _ p)) -- Lean _ infers? 
private lemma ups_g (a:Axis)(g:Cover→E)(V:LinksC): jumpsC o a (gauge g V)= gauge (g ∘ (pole a o).motion) (jumpsC o a V):=by
 funext e; let v:=gauge g V; let S:= Signed.mirror a; change ((posDir e.2).rotate S).read _ ((pole a o).motion e.1)=_; rw [Step.gauge_read]; unfold Lattice.gauge; dsimp only [Function.comp_apply, moveC, jumpsC, Pivot.pole, Lattice.pull]; rw [Shape.motion_v]; rw [Step.vec_rotate,Step.vec_pos]; rfl -- `pole` Tundra formula.
lemma sky_mask(A:Finset (Face ℤ))(u:ℝ) : GaugeInvariant ((bedH A u)∘ leaps o):=by
 intro g i; dsimp only [Function.comp_apply]; unfold leaps; rw [ups_g,ups_g,ups_g,bedColour]
lemma pure_sky(X:LinksC)(t:PureZ X): PureZ (leaps o X):=by
 have hz(a:Axis)(f:LinksC)(t:PureZ f): PureZ (jumpsC o a f):=by
    let g:= (limbP o).rootF f; have he:gauge g f=1:= t.owns _; let T:=g ∘ (pole a o).motion; have ht:gauge T (jumpsC o a f) = jumpsC o a 1:=by unfold T; rw [←ups_g,he]
    have h1: jumpsC o a 1=1:=by funext e; unfold jumpsC moveC Lattice.pull Step.read; split <;> simp
    intro i; calc
     _= SU.group.chord (faceValue (gauge T (jumpsC o a f)) i):=by rw [face_gauge,SU.group.chord_conj]
     _=0:= by rw [ht,h1]; simp [faceValue,square,travel] -- tune
 exact hz 0 _ (hz 1 _ (hz 2 X t))
def bedP (f:LinksC):ℂ:= bedH A t f* bedH A t (leaps o f)
lemma bedP_color: GaugeInvariant (bedP o A t):=by intro g i; exact congrArg₂ (·*·) (bedColour A t g i) (sky_mask o A t g i) -- jointly
lemma bedP_cont : Continuous (bedP o A t) := (bedH_cont ..).mul ((bedH_cont ..).comp (leaps_cont o))
lemma bedP_fee (V:LinksC): ‖bedP o A t V‖ ≤ 1:=by rw [bedP,norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (bedH_bound ..)).trans (bedH_bound ..)
lemma bedP_here : bedP o A t ∘ onC N= sapW o (bedH A t ∘ onC N) :=by funext i; unfold bedP sapW; rw [Pi.mul_def]; dsimp only [Function.comp]; rw [leaps_here]; -- tune
lemma bedP_local {r:ℕ}(v:carpet A ⊆ Quest.scape o r) : Lattice.LocalOn (Quest.scape o r) (bedP o A t):=fun x y h=> congrArg₂ (·*·) (bedH_local A t x y (fun i p t=> h i (v p) (v t))) (bedH_local A t _ _ (fun i p t=> (leaps_agree o (show Agrees (πS o (Quest.scape o r)) x y from by rwa [jumps_cover])) i (v p) (v t)))
local notation "f_Ω"=> fun x:LinksC=> ∑ i∈A,(SU.group.chord (faceValue x i))
lemma bedP_security (p:0<t): ∃ U:Finset (Face ℤ), ∃ b:ℝ,0<b∧∀ c:ℝ,c≤ b→∀ x:LinksC, ¬alarm U c (x,x) → bedP o A t x=1:=by
 let F(x:LinksC):= (f_Ω) x; have h:Continuous F:= continuous_finsetSum _ (fun i _=> by unfold faceValue; fun_prop); have he(x:LinksC):0 ≤ F x:=sum_nonneg (fun i _=>SU.group.chord_nonneg _); have ht(x:LinksC)(p:PureZ x):F x=0:=sum_eq_zero fun i _=> p i;
 obtain ⟨U,c,q,X⟩:=pension (h.add (g:=fun x=>F (leaps o x)) (h.comp (leaps_cont o))) (fun i v=>(by change F i+F (leaps o i)=_; rw [ht i v,ht _ (pure_sky o i v),add_zero])) t p
 have hz(x:LinksC)(t':F x ≤ t): bedH A t x=1:= by refine bed_lords p ?_; intro h; obtain ⟨i,h,p⟩:=h; exact p.not_ge ((single_le_sum (f:=fun j=> SU.group.chord (faceValue x j)) (fun i _=>SU.group.chord_nonneg _) h).trans t')
 refine ⟨U,c,q,fun b t' x p=>?_⟩; obtain Q:= X b t' x p; unfold bedP; rw [hz x ((le_add_of_nonneg_right (he (leaps o x))).trans Q), hz (leaps o x) ((le_add_of_nonneg_left (he x)).trans Q), mul_one]
#print axioms bedP_security
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
#print axioms YM.CF.Window.Pivot.cutBoth
