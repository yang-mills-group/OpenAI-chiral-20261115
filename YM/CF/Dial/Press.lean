import YM.CF.Peaks.Waltz
import YM.CF.Rush.Rhoda
import YM.CF.Cubes.Candidate
/-! Paired cylinder domains, simultaneous unbounded fermion history. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N P : Side}
-- fields on gauge sites
abbrev Stun(N:Side):= Site (More N)→ Cube.Ballot
def hook(x:Stun N)(i:Site (More N)):Vect:=(x i).val
lemma hookN(x:Stun N)(i):‖hook x i‖=1:=vote_unit _
def feast(g:Site (More N)→ E)(x:Stun N): Stun N:=fun i=> scaledV (g i) (x i)
lemma hookF(g:Site (More N)→E)(x:Stun N): hook (feast g x)=turnX g (hook x):=rfl
abbrev QuiltF:=SpinIdx×Slot
abbrev Spool(N:Side):= Site (More N)→ Bool → Op QuiltF
def palt (X:Stun N): Spool N:=fun z u=> if u then localPair (hook X z) else star (localPair (hook X z))
abbrev coinK(g:E): UNI QuiltF:= ⟨color matter g,color_mem ..⟩
def heat(g:Site (More N)→ E)(x:Spool N): Spool N:=fun i b=>
    let V:=coinK (g i); let W:=ccU V
    if b then V.val*x i b * star W.val else W.val*x i b *star V.val
lemma heat_palt (g:Site (More N)→E)(x:Stun N): heat g (palt x)=palt (feast g x):=by
  funext i u; let K:=coinK (g i); let T:=ccU K; let C:=localPair (hook x i)
  have hp: localPair (hook (feast g x) i)=K.val*C*star T.val:=(localPair_turn ..).trans (congr_form K C)
  cases u
  · change T.val*star C*star K.val=star (localPair _); rw [hp,star_mul,star_mul,star_star, mul_assoc]
  change K.val*C*star T.val=localPair _; rw [hp]
lemma heat_d (V W : UNI QuiltF) (X Y:Op QuiltF): ‖V.val*X*star W.val - V.val*Y*star W.val‖=‖X-Y‖:= by rw [←sub_mul,←mul_sub, show star W.val=(star W).val from rfl, CStarRing.norm_mul_coe_unitary _ (star W), CStarRing.norm_coe_unitary_mul]
lemma heat_norm (g:Site (More N)→E)(x y:Spool N): ‖heat g x-heat g y‖=‖x-y‖:=by
  have he(i)(u):‖heat g x i u-heat g y i u‖=‖x i u-y i u‖:=by cases u; exact heat_d ..; exact heat_d ..
  have ht(i):‖heat g x i-heat g y i‖=‖x i-y i‖:=by
    apply le_antisymm<;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun u=>?_
    · exact (he i u).le.trans (norm_le_pi_norm (x i -y i) u)
    exact (he i u).ge.trans (norm_le_pi_norm (heat g x i-heat g y i) u)
  apply le_antisymm<;> refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i=>?_
  · exact (ht i).le.trans (norm_le_pi_norm (x-y) i)
  exact (ht i).ge.trans (norm_le_pi_norm (heat g x-heat g y) i)

abbrev Sew(N P:Side):= Nom N P × (Stun P×Stun N)
abbrev Bale(N P:Side):= Coil N P× (Spool P×Spool N)
def post (x:Sew N P):Bale N P:=(unionP x.1,palt x.2.1,palt x.2.2)
variable (G:Ratio N P)
structure Gild (x:Sew N P)(e:ℝ): Prop where
 covW : JointB G x.1 e
 loS : Slow x.1.1 (hook x.2.1) e
 hiS : Slow x.1.2 (hook x.2.2) e
 pegS : ∀ i, ‖hook x.2.1 ((ratio G).embed i)-hook x.2.2 i‖ < e

def zoneP(e:ℝ): Set (Bale N P):= {x|∃ U:Sew N P,Gild G U e∧ ‖x-post U‖<e}
lemma zoneK(e:ℝ):IsOpen (zoneP G e):=by rw [show zoneP G e=⋃ i:{U:Sew N P//Gild G U e}, ball (post i.val) e by ext; simp [zoneP, Metric.mem_ball,dist_eq_norm]]; exact isOpen_iUnion fun _=>isOpen_ball
lemma Gild.breadth{e b:ℝ}{x:Sew N P}(h:Gild G x e)(p:e≤b): Gild G x b:= ⟨⟨h.covW.fg.shrink p,h.covW.cg.shrink p, fun i=>(h.covW.follow i).trans p⟩,fun i j=>(h.loS i j).trans_le p,fun i j=>(h.hiS i j).trans_le p,fun i=>(h.pegS i).trans_le p⟩
lemma portland {x:Bale N P}{e b:ℝ}(h:x∈ zoneP G e)(p:e≤b):x∈zoneP G b:=by obtain ⟨u,h,f⟩:=h; exact ⟨u,h.breadth G p,f.trans_le p⟩
lemma silk (x:Bale N P){e:ℝ}(h:x∈ zoneP G e):x.1∈legal G e:=by obtain ⟨u,h,f⟩:=h; exact ⟨u.1,h.covW,(norm_fst_le (x-post u)).trans_lt f⟩
def frost (g:Site (More P)→ E)(x:Sew N P) : Sew N P:=(july G g x.1,feast g x.2.1,feast (scaleG G g) x.2.2)
def novel (g:Site (More P)→E)(x:Bale N P): Bale N P:= (jazz G g x.1,heat g x.2.1,heat (scaleG G g) x.2.2)
lemma speak(g:Site (More P)→E)(x:Sew N P): novel G g (post x)=post (frost G g x):=by simp [frost,novel,post,heat_palt,jig]
lemma solid(g:Site (More P)→E) {x:Sew N P}{e:ℝ}(h:Gild G x e): Gild G (frost G g x) e:=by
  refine ⟨joint_g _ _ h.covW g,slow_g _ _ g h.loS,slow_g _ _ _ h.hiS,fun i=>?_⟩
  change ‖turn (g ((ratio G).embed i)) _-turn (g ((ratio G).embed i)) _‖<e; rw [←turn_sub,turn_norm]; exact h.pegS i
lemma novel_r (x y:Bale N P)(g:Site (More P)→E): ‖novel G g x-novel G g y‖=‖x-y‖:=by simp only [novel,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,heat_norm, jazz,relayg_eq]
lemma cyl (g:Site (More P)→E)(x:Bale N P){e:ℝ}(h:x∈zoneP G e): novel G g x∈zoneP G e:=by
  obtain ⟨u,h,f⟩:=h; refine ⟨frost G g u,solid G g h,?_⟩; rw [←speak,novel_r]; exact f
omit G
lemma close_tick (ε:ℝ)(h:0<ε):∃ δ:ℝ,0<δ ∧ ∀ {N:Side}(x y:Stun N)(i j), ‖hook x i-hook y j‖<δ → ‖palt x i-palt y j‖<ε:=by
  have ht:Continuous (fun v:Ballot => fun u:Bool=>if u then localPair v.val else star (localPair v.val)) := by
    apply continuous_pi; intro i; cases i; exact (localPair_cont.comp continuous_subtype_val).star; exact localPair_cont.comp continuous_subtype_val
  obtain ⟨δ,p,h⟩:= Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous ht) ε h -- tune
  exact ⟨δ,p,fun {N} x y i j H=> by
    have hx:= h (show dist (x i) (y j)<δ by rw [Subtype.dist_eq,dist_eq_norm]; exact H); rw [dist_eq_norm] at hx; exact hx⟩
def apex :Ballot:= ⟨basisKet 0,by simp [Sphere,basisKet]⟩
lemma apex_eq (x:Ballot):∃ g:E,x=scaledV g apex:=by
  obtain ⟨g,h⟩:=Pair.reachable x.val (vote_unit x); refine ⟨g,Subtype.ext ?_⟩; apply PiLp.ext; intro i; rw [← h]; rfl

def vacuumW(N:Side):Stun N:=fun _=>apex
include G
lemma tone(e:ℝ)(h:0<e): Gild G (1,vacuumW P,vacuumW N) e :=by
  let X: Nom N P:=1
  have he{N:Side} : Slow (1:Bkg (More N)) (fun y=>apex.val) e:=by intro z i; change ‖turn 1 _-_‖<e; unfold turn; rw [fund_one,act_one,sub_self,norm_zero]; exact h -- fix binder
  have hh (l:Walk)(x:Site (More P)): travel X.1 x l=1:=by induction l generalizing x with | nil=> rfl| cons a l ih=>rcases a with ⟨a,l'|l'⟩ <;> simp [X,Step.read,travel] at ih ⊢ <;> exact ih _
  exact ⟨⟨guard0 h.le,guard0 h.le,fun i=>by rw [hh _]; change ‖brand 1-brand 1‖≤_; simp [h.le]⟩,he,he,fun i=>by change ‖apex.val-apex.val‖<e; simpa⟩
end YM.CF.Dial
