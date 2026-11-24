import YM.SU5.FiniteGaugeData.Nine.Oscar
import YM.SU5.FiniteGaugeData.Eight.Outlive
/-! # Bare spatial mirror test, handedness NOT ROTATED. We don't presume parity symmetry.
 native & Family level (ALL allowed by Probe). -/
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
open Buffered.Afterglow.Hierarchy -- Port ambiguous!
section trans
variable (a b:Shape)(N:Side)
abbrev imageR (A:Op (Single N)) := twist (prepU a 1 inert N) A
abbrev imageQ(N:Side)(A:FC (Single N)) := twist (quantU (prepU a 1 inert N)) A
def rollR (a:Shape){N:Side}(y:Fields N) := Prod.map (Yg a) (Yg a) y
/-- Want composition `twist U (f(move?))`: on covariant field f transforms on ALL fields; gauge equiv when Φ generation 'gauge(g) x' yields f(move'(x))=f'+ gauge(g∘p.anon), combine U_a requires composing with .anon AGAIN. Thus actual a^−¹ on rollR. For polar or mirror a invol. Composition until T argument commutes. -/
def castT (a b:Shape){N:Side}(f:Mark N):Mark N:=fun i=> imageQ a N (f (rollR b i))
abbrev pageF (f: Mark N):= castT (polarQ o) (polarQ o) f
private lemma credit_Q (A B: UNI (Single N)): quantU (A*B)=quantU A*quantU B:= Subtype.ext (quant_mul ..)
lemma screw_point (A:FC (Single N)): imageQ (joinX a b) N A=imageQ b N (imageQ a N A):=by
 unfold imageQ; nth_rw 1 [← mul_one (1:UNI SpinIdx),← kio]; rw [credit_Q,Fock.twin]
lemma wind_fields (x:Fields N): rollR (joinX a b) x= rollR b (rollR a x):= by simp only [rollR,Prod.map,kor]
lemma cast_turn (u v:Shape)(f:Mark N): castT b u (castT a v f)=castT (joinX a b) (joinX u v) f:=by funext i; rw [castT,castT,castT,screw_point, wind_fields] -- composition wind R (v after u)
lemma blankR(x:Pane N): Yg (incX 1) x=x:= Nacre.blank ..
lemma erasing (f:Mark N):castT (incX 1) (incX 1) f=f:=by  have O(x:Fields N): rollR (incX 1) x=x:= Prod.ext (blankR ..) (blankR ..); funext i; rw [castT,O,imageQ, prep_one, show quantU (1:UNI (Single N))= (1:UNI (Finset (Single N))) from Subtype.ext quant_one,one_des]
local notation "R"=> (polarQ o)
lemma page_twice (f:Mark N):pageF o N (pageF o N f)=f := by -- order pageF includes o,N
 rw [pageF,pageF,cast_turn,polar_id,erasing]
variable (e:ℝ)
lemma anon_mixed (x:Seat N): (joinX a b).anon N x=a.anon N (b.anon N x):=by rw [←Rush.nat_true x, Shape.anno,palm,← Shape.anno,← Shape.anno]
lemma anon_sky (x:Seat N): (R).anon N ((R).anon N x)=x:=by rw [←anon_mixed,polar_id]; simp [incX, Shape.anon, affine]
lemma moves_W (S:Support (More N)): twist (Port o N) (cutM (modesIn N S))=cutM (modesIn N (S.image ((R).anon N))):= by
 apply prep_moves; intro x; exact ⟨fun u=>by obtain ⟨y,v,rfl⟩:=mem_image.mp u; rwa [anon_sky],fun v=>mem_image.mpr ⟨_,v,anon_sky ..⟩⟩
lemma moves_H : twist (Port o N) (cutM (Tset N))=cutM (Tset N):=by
 apply Mir.twist_comm; ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,l⟩,t⟩; simp only [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul, grade_one]
 let P(x:Site N):= ((R).payA x) • ((1:Op SpinIdx) ⊗ₖ (1:Op SU.Slot)); change jump _ P (x,(i,j)) (y,(l,t)) * _ = _ * jump _ P (x,(i,j)) (y,(l,t)) -- `_` eta may fail
 rw [jump_apply]; by_cases h:i=l; · subst i; by_cases v:l∈ plusHalf <;> simp [v] -- eta
 split<;>simp [P,h] -- tune
lemma marble_image {T:Support (More N)}{A:Op (Single N)}{n:ℕ} {B:FC (Single N)} (v:Mirage.Marble A T n B e) : Mirage.Marble (twist (Port o N) A) (T.image ((R).anon N)) n (imageQ R N B) e:=by
 let U:= Port o N; let S:= cutM (Tset N); let Q:=mateK N; let F:= acts (quantU U).val Q; have h:Sea (cutM (Tset N)) Q:= touchP N ▸ tickB N
 have hz:Sea S F:=by
    refine ⟨?_, (act_unit_norm ..).trans h.2⟩; unfold F; nth_rw 1 [← (show twist U S=S from moves_H o N),line_twist,←Fock.swivel]; rw [(show acts (lineOp S) Q=_ from h.1)] -- tune let
 have hv : Q=inner ℂ F Q • F:=h.1.symm.trans (hz.scalar (cutM_idp _) _)
 obtain ⟨D,x,p,w,v,j⟩:=v.prize
 let L:= Fock.Brique.Full.swirled v U; refine ⟨twist U D,x.twist_t U (moves_W o N T),rot D p _,(trace_twist ..).trans w,?_,?_⟩; · change Full _ (acts _ Q); intro y ht; unfold imageQ; rw [hv,←map_star,map_smul,(show acts _ (F) = _ from (Fock.swivel (quantU U) (star B) Q).symm),map_smul, (L y ht),smul_zero] -- syntax
 rw [←map_mul]; exact (twist_norm ..).trans_le j
lemma pollen (T:Shape)(g:Seat N→SU.E) (A:FC (Single N)): imageQ T N (Brique.flipsP g A)= Brique.flipsP (g ∘ T.anon N) (imageQ T N A):=by unfold imageQ Brique.flipsP; rw [←Fock.twin,←Fock.twin,← credit_Q,←credit_Q,envoy]
lemma page_cost(x:Mark N)(y:Fields N): ‖pageF o N x y‖=‖x (rollR R y)‖:= twist_norm ..
lemma page_title {x:Mark N}(p:Buffered.covariant x): covariant (pageF o N x):=by
 intro g u; unfold pageF castT; rw [show rollR R (simultaneous g u)=simultaneous (g∘ (R).anon N) (rollR R u) from Prod.ext (van ..) (van ..), p]; change imageQ R N (Brique.flipsP _ _)=Brique.flipsP _ _; rw [pollen,show (g∘ _)∘ (R).anon N=g from funext fun i=> congrArg g (anon_sky ..)]
end trans
end YM.CF.Window.Pivot
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Tenant Fock Tulip Dial Fir Ember Buffered Skye Scree Nacre
attribute [local instance] opCStarAlgebra
open Window Mir Phase RP Largo Spire Reflect
open Fock.Brique Lifted Girt
open Window.Pivot
set_option quotPrecheck false
variable (i:Axis)(o:Cover)
local notation "T"=> pole i o
local notation "R"=> polarQ o
variable (K:Calibration)
def imagePlane (N:Shape) (f:Family K): Family K:=fun m=> castT N N (f m)
def pageP : Family K→ₗ[ℂ] Family K where
 toFun := imagePlane K (polarQ o) -- tune
 map_add' f g := funext fun _=> funext fun _=> map_add ..
 map_smul' a f := funext fun _=>funext fun _=> twist_scalar ..
local notation "Ρ"=> pageP o K
lemma page_proj (f:Family K): pageP o K (pageP o K f)=f:= funext fun _=> page_twice o _ _
lemma page_words (F:Family K): pageP o K F=imagePlane K (polarQ o) F:=rfl -- tune
-- in chosen assembly order planes 0 outside 2
lemma cast_image (x:Family K):pageP o K x=imagePlane K (pole 0 o) (imagePlane K (pole 1 o) (imagePlane K (pole 2 o) x)):=by
 funext i; unfold imagePlane; change castT (polarQ o) (polarQ o) (x i)=_; rw [cast_turn,cast_turn]; unfold polarQ; rw [←(show joinX (joinX (pole 2 o) (pole 1 o)) (pole 0 o)=joinX (pole 2 o) (joinX (pole 1 o) (pole 0 o)) from ?_), pole_inter o (by decide:(0:Axis)≠1)] -- tune target rollR join u v: b=0 u=0 a=(join2 1) v=join1 2; join u v=(join 0 (join 1 2)). want reversed. compare powers. simpler composition we don't need separate b; reverse via commute using polar equality. 
 · have he(a b c:Shape): joinX a (joinX b c)=joinX (joinX a b) c:=by unfold joinX; simp [Signed.act_mul,mul_assoc,add_assoc]
   rw [← he (pole 1 o) (pole 0 o) (pole 2 o), pole_inter o (by decide : (0:Axis)≠2), he, pole_inter o (by decide:(1:Axis)≠2)] -- may `he` rewrite joinX? examine
 unfold joinX; simp [Signed.act_mul,mul_assoc,add_assoc]
variable {S U:Finset Cover} {σ : Window.Family} {t: List Cover}{X Y:Family K}
abbrev πS (S:Finset Cover):= S.image ((polarQ o).motion)
local notation "G"=> refract i (o i)
local notation "B"=> imagePlane K (pole i o)
lemma planeB_add (x y:Family K): B (x+y)= B x+B y:= funext fun _=> funext fun _=> map_add ..
lemma planeB_zero : B 0=0:=funext fun _=> funext fun _=> map_zero _
lemma imageOne (N:Side)(U:Shape):twist (quantU (prepU U 1 inert N)) (1:FC (Single N))=1:=by rw [twist_formula,mul_one]; exact (quantU (prepU ..)).property.2
lemma planeB_one : B 1=1:= funext fun _=> funext fun _=> imageOne _ _
lemma planeB_s (x:Family K)(z:ℂ) : B (z•x)=z • B x:= funext fun _=> funext fun _=> twist_scalar ..
lemma planeB_mu (x y:Family K): B (x*y)=B x* B y:= funext fun _=> funext fun _=> map_mul ..
lemma poseC (N:Side)(x:Cover)(l:SpinIdx)(b:SU.Slot) : acts (prepU T 1 inert N).val (basisC N x l b)= basisC N ((T).flee x) l b :=by
 apply PiLp.ext; rintro ⟨⟨y,j⟩,t⟩; simp_rw [basisC,map_smul,WithLp.ofLp_smul,Pi.smul_apply,basis_apply,basis_act]; let v:= wrap N ((T).flee x)
 have hp:Tofu T N v=wrap N x:=by change (T).mills N v= _; rw [show v=_ from (Shape.mill T x).symm, pole,matter_invol]
 have he : (prepU T 1 inert N).val ((y,j),t) (Lifted.index N x l b)= if y=v then (T).payA y * ((1:Op SpinIdx) j l*(1:Op SU.Slot) t b) else 0:=by
    change jump (Tofu T N) (fun i=>(milU T 1 inert i).val) (y,j,t) (wrap N x,l,b)=_; rw [jump_apply]; by_cases h:y=v; · rw [if_pos h,if_pos (show Tofu T N y=_ from h.symm ▸ hp)]; rfl
    rw [if_neg h, if_neg (fun e=> h ((Tofu T N).injective (e.trans hp.symm)))]
 change (Lifted.winding N x) • (prepU T 1 inert N).val ((y,j),t) _=_; rw [he]; by_cases h:y=v; · subst y; by_cases p:j=l <;>by_cases q:t=b <;>simp [Lifted.index,p,q,v,pole,Matrix.one_apply]<;> (first | (subst t; subst j; simp [winding_frame])| skip)
 unfold v at h; simp [h,Lifted.index,v]
lemma pose_UP(x:Cover)(j:SpinIdx)(b:SU.Slot): B (creation K x j b)=creation K ((T).flee x) j b:=by funext m y; rw [imagePlane,castT,imageQ,creation,creation,twist_create,poseC]
lemma pose_LO(x:Cover)(j:SpinIdx)(b:SU.Slot): B (removal K x j b)=removal K ((T).flee x) j b:= by funext m y; rw [imagePlane,castT,imageQ,removal,removal,twist_remove,poseC]
def c₁(F:PairsC→ℂ):=F∘ Prod.map (moveC i (o i)) (moveC i (o i))
lemma pose_SEED(F:PairsC→ℂ): B (scalar K F)= scalar K (c₁ i o F):=by
 funext m v; unfold imagePlane castT scalar rollR; rw [imageQ, twist_scalar,imageOne]; apply congrArg (fun u:ℂ=> u • 1); unfold c₁; simp only [Prod.map_fst,Prod.map_snd, Function.comp]; unfold moveC; simp_rw [show Yg T= fling i (o i) (K.c m) from rfl, reflect_onC]; rfl
lemma pose_coeff (F:PairsC→ℂ){u:Bool}(p:Coeff u S F): Coeff u (G S) (c₁ i o F):=by
 refine ⟨fun v=> ?_, Push.SectorMeasure.Env.along (g:=Prod.map (moveC i (o i)) (moveC i (o i))) p.env ((Continuous.prodMap (move_cont ..) (move_cont ..)).measurable), fun x y u v=>p.locus (Prod.map _ _ x) (Prod.map _ _ y) (moved_agree _ _ u) (moved_agree _ _ v)⟩; obtain ⟨q,u,w⟩:=p.narrow v; rw [w]; exact ⟨q∘ moveC i (o i),u.comp (move_cont ..),rfl⟩
lemma pose_struct {u b:Bool}(p:InTest K u S b X): InTest K u (G S) b (B X):=by
 induction p with
 | creator b p v=>rw [pose_UP]; exact .creator b p (mem_image.mpr ⟨_,v,Shape.mote ..⟩)
 | remover b p v=> rw [pose_LO]; exact .remover b p (mem_image.mpr ⟨_,v,Shape.mote ..⟩)
 | seed p=>rw [pose_SEED]; exact .seed (pose_coeff i o _ p)
 | zero=> rw [planeB_zero]; exact .zero
 | one=> rw [planeB_one]; exact .one
 | add _ _ p v=>rw [planeB_add]; exact .add p v
 | mul _ _ p v=>rw [planeB_mu]; exact .mul p v
 | smul b _ p=>rw [planeB_s]; exact .smul _ p
lemma pose_table (p:Tableau K σ U S t X): Tableau K σ (G U) (G S) (t.map ((T).flee)) (B X):= by
 induction p with
 | ident=>rw [planeB_one]; exact .ident
 | zero=>rw [planeB_zero]; exact .zero _
 | pair _ x y v l j a b lt ut p q H=>simp_rw [planeB_mu,pose_UP,pose_LO]; exact H.pair _ _ (mem_image.mpr ⟨_,v,Shape.mote ..⟩) _ _ _ _ lt ut p q
 | add _ _ a b=> rw [planeB_add]; exact .add a b
 | scale _ x a=>rw [planeB_s]; exact a.scale _
 | gauge _ W p a=>rw [planeB_mu,pose_SEED]; exact a.gauge _ (pose_coeff i o _ p)
lemma pose_tableau (p:Copse K S U σ t X): Copse K (G S) (G U) σ (t.map ((T).flee)) (B X):=by
 let g:= (T).flee; let h:Function.Injective g := (show Involutive g from fun _=> flee_twice ..).injective
 refine ⟨fun e=> p.walk (List.map_eq_nil_iff.mp e), p.strand.map h, image_subset_image p.rear, ?_,?_,pose_table i o K p.output,fun m v x=>?_⟩
 · intro x v; obtain ⟨w,t,rfl⟩:= List.mem_map.mp v; exact mem_image.mpr ⟨_,p.front w t,Shape.mote ..⟩
 · intro x v u; obtain ⟨w,y,rfl⟩:= List.mem_map.mp v; obtain ⟨k,t,z⟩:= mem_image.mp u; have he:Injective (T).motion:= (show Involutive (T).motion from (fun i₁=>by rw [← palm,gaugeSquare]; simp [incX, Shape.motion])).injective; exact p.gap w y ((show k=nodeC w from (he (z.trans (Shape.mote ..).symm))) ▸ t)
 let F:=X m; unfold imagePlane castT; rw [show rollR T (simultaneous v x) = simultaneous (v∘ (T).anon _) (rollR T x) from Prod.ext (van ..) (van ..), p.coin m]; change imageQ T (K.c m) (Window.Brique.flipsP _ _)=Window.Brique.flipsP _ _; rw [pollen,show (v∘ _)∘ (T).anon (K.c m)=v from funext fun i=> congrArg v (fling_there ..)]
private lemma α (x:Cover)(k:Axis)(a b:Axis)(t:a≠b):(pole a o).motion ((pole b o).motion x) k = (pole b o).motion ((pole a o).motion x) k:=by apply congrFun _ k; rw [←palm,←palm,pole_inter o t] -- syntax maybe apply
lemma pi_party(S:Finset Cover): πS o S= refract 0 (o 0) (refract 1 (o 1) (refract 2 (o 2) S)):=by
 unfold refract πS; rw [image_image,image_image]; apply congrArg (fun a=> image a S); funext x; apply funext; intro i; rw [palm_vis]; unfold Buffered.plane; change _= (pole 0 o).motion ((pole 1 o).motion ((pole 2 o).motion x)) i; unfold pole; simp_rw [fling_move]; fin_cases i<;> (norm_num [Axis,Fin.ext_iff] <;> simp (config := {failIfUnchanged:=false}) [show (⟨2,by decide⟩:Fin 4)=2 from rfl]<;> omega)
lemma pi_narrow{b c:Bool}(h:InTest K b S c X): InTest K b (πS o S) c (pageP o K X):=by rw [pi_party,cast_image]; exact pose_struct _ o K (pose_struct _ o K (pose_struct _ o K h)) -- Lean .. fills trailing not leading
lemma pi_pure(p:Tint.Durable K X): Tint.Durable K (pageP o K X):= fun m=> page_title o _ (p m)
lemma pi_revenue (h:Copse K S U σ t X): ∃ x:List Cover,Copse K (πS o S) (πS o U) σ x (pageP o K X):=by rw [pi_party,pi_party,cast_image]; exact ⟨_,pose_tableau 0 o K (pose_tableau 1 o K (pose_tableau 2 o K h))⟩
#print axioms pi_narrow
#print axioms pi_revenue
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
#print axioms YM.CF.Window.Pivot.marble_image
