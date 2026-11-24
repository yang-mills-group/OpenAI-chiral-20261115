import Anomaly.Ward.RankCost
import Anomaly.Ward.Dye
import YM.SU5.Silk.Clock.Glide
/-!
Linearized action on link scans and the tested determinant-type affine top chord.
Preserve chirality in calculating $Z'_s$; no moving H projection outside real cost yet.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire -- tune
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 24000
variable {N: Side}
/-! H. Signs. `spinZ`. mPath works on full group.
Pin sweep *fixing the odd site used for every root's strand test*. -/
def gridTulip(s: Signed)(x:Site N): Sweep N:= by
 let V:=(across_m x x s).choose
 exact ⟨V.s,V.b,detX s⟩
lemma tieS(s:Signed)(x:Site N) : (gridTulip s x).s=s:= (across_m x x s).choose_spec.2.1
lemma tieC(s:Signed)(x:Site N) : (gridTulip s x).charge=detX s:=rfl
lemma tieA(s:Signed)(x:Site N) : mPath (gridTulip s x) x=x := (across_m x x s).choose_spec.2.2
abbrev dollar(s:Signed):ℝ:=if detX s then -1 else 1
lemma dollar_fixed(s:Signed):|dollar s|=1:=by unfold dollar; split <;> norm_num
lemma dollar_mul(s t:Signed):dollar (s*t)=dollar s*dollar t:=by cases h:detX s <;>cases p:detX t<;>simp [dollar,det_p,h,p]
lemma sew_tag (w:Sweep N)(y x :Site N): mPath w (y+x)= w.s.act y + mPath w x:=by
 apply node_inj N; rw [nodeA,node]
 -- unfold correct
 rw [node, map_add (assembly N).root (w.s.act y) (mPath w x)]; have hp:= nodeA w x
 rw [sitA] at *; unfold node at hp; rw [add_assoc ((assembly N).root _) ((assembly N).root _) 1,hp]; unfold affine; simp only [map_add,Signed.act_add,Ratio.root_embed,Ratio.signed]; abel
lemma tie_wrap (s:Signed)(u:Cover): mPath (gridTulip s (0:Site N)) (wrap N u)=wrap _ (s.act u):=by
 let V:=wrap N u
 rw [show wrap N u= V+(0:Site N) from (add_zero V).symm,sew_tag,tieA,tieS,add_zero]; exact Lattice.wrap_signed .. -- tune

lemma tie_unique(s:Signed)(x:Site N)(V:Sweep N)(v:V.s=s)(t:V.charge=detX s)(p:mPath V x=x):gridTulip s x=V:=by
 have hp:boxA V (node x)=boxA (gridTulip s x) (node x):=by rw [←nodeA,p,←nodeA,tieA] -- tune order
 rw [sitA,sitA,tieS,v,affine,affine] at hp; have hx:(gridTulip s x).b=V.b:=(assembly N).embed_injective (add_left_cancel hp.symm)
 exact sweep_ext (tieS s x |>.trans v.symm) hx (tieC s x|>.trans t.symm)
where sweep_ext {a b:Sweep N}(h:a.s=b.s)(w:a.b=b.b)(p:a.charge=b.charge):a=b:=by cases a; cases b; congr
lemma tieMul (s t:Signed)(x:Site N): gridTulip (s*t) x=gridTulip s x*gridTulip t x:=by
 apply tie_unique _ _ _ (show (gridTulip s x).s * (gridTulip t x).s=_ from by rw [tieS,tieS]) (det_p s t).symm; rw [←mPath_seq,tieA,tieA]
lemma tieOne (x:Site N): gridTulip 1 x=1:=tie_unique _ _ _ rfl det_i.symm (mPath_one x)
lemma millT(s:Sweep N)(x:Site N): ech s (millQ (mPath s x))= millQ x:=by rw [millSt,millSt,nodeA]; exact Tye.proM (boxA _) (boxA _).injective s.charge (γS s) (fun i j h=>Tye.birth_l _ _ _ _ _ h) _

open Py Py.Rate Py.Rate.LocalLimit Py.Rate.LocalLimit.Preparation
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}{J:Course P F}{i k s m:ℕ}{a b c d:ℝ}{X Z R K}
-- same P candidate proviso collapses rank.At ALL guard consultations. Need only real.
def tapestryQ (P:Preparation)(M:Tulip.Male)(n:Side)(V:Pane n):= funde P.K.j M n (profile V)-tickA n
lemma weaveT (s:Signed)(x y: Site N)(V:Pane N)(M:Tulip.Male)(p:Guard V P.d)(h:P.U.roundZ ≤ N.val) : let g:=gridTulip s x
 (siteRead y (tapestryQ P M N (flashA g V))).re= dollar s*(siteRead (mPath g y) (tapestryQ P M N V)).re:=by
 intro g; let A:=funde P.K.j M N; let T:= Levier.spinU g.charge g.s
 have hk: A (profile (flashA g V))=swapX (detX s) (ech g (A (profile V))):=by
    have hQ : ech g (A (profile V))= swapX (detX s) (A (profile (flashA g V))):=by
       rw [← show g.s=s from tieS ..]
       exact funde_f (castX g) (xtra g.charge) T (Levier.spinZ ..) V _ (by rw [P.kJ]; omega) M _ (P.V.note.fields_one _ (P.U.needed.trans h)) (p.shrink P.U.gem)
    rw [hQ]; unfold swapX; split <;> first|rfl|abel
 have hτ:swapX (detX s) (ech g (tickA N))=tickA N:=by
    rw [touchP,←show g.s=s from tieS .., show ech g _ = swapX (detX g.s) (cutM (Tset N)) from tickR _ (xtra g.charge) T (Levier.spinZ ..) _]; unfold swapX; split <;> first| rfl| abel
 let S:=tapestryQ P M N V; let W:= S*millQ (mPath g y)
 have hv:tapestryQ P M N (flashA g V)= dollar s • ech g S:=by
    have ht: ech g (A (profile V)-tickA N)= ech g (A (profile V))-ech g (tickA N):=by unfold ech sings; rw [win_l,map_sub]
    change A _-tickA N=dollar _ • ech g (_- _); rw [hk,ht]; nth_rw 1 [←hτ]; unfold dollar swapX; split <;> simp [sub_eq_add_neg] <;> abel
 have hw: (Matrix.trace (ech g W)).re=(Matrix.trace W).re:=by unfold ech sings; rw [trace_twist,win_trace]; unfold cSignX; split <;>simp
 rw [←mill_read, ←mill_read,hv,Matrix.smul_mul,Matrix.trace_smul]; change (dollar s • Matrix.trace (ech g S*millQ y)).re= _ ; rw [←millT g y,show ech g _ * ech g _= ech g W from ?_, Complex.real_smul,Complex.re_ofReal_mul,hw]
 unfold W ech sings; rw [win_m,map_mul]
end YM.CF.Swell.Sonar
