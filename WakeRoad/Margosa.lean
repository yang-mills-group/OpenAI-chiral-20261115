import WakeRoad.Canarium
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Shelter
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.WakeRoad
open Function Filter Metric Lattice Wilson Laurent Finset RG
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Classical
open CF CF.Cube CF.Gingham.Ruff CF.Skye CF.Tulip CF.Lat CF.Scree PhysicalNext.JointLoad.Heir YM.ConnectedActivityE6
open CF.Buffered CF.Buffered.Afterglow.Tower.VacuumSelection
open CF.Buffered.EmberWind
open Spine.Gingham.VoyageB
open Work.E08
variable {N:Side}
local notation "K"=>CF.SU.group
local notation "l"=> CF.SU.group.Color
local notation "€"=> CF.SU.E
-- use centered Pinwax and track its variation
open CF.Pannier.Chancel.Rous
abbrev shore (o:Seat N)(m:ℕ):= halo m {o}
lemma shoreq(o:Seat N)(m:ℕ)(x:Seat N) :x∈ shore o m↔separation o x ≤ m:=by rw [shore,halo_spec]; simp
private lemma coach(r:ℕ)(o y z:Seat N)(p:y∈ shore o r)(h:z∈ visits o (march o y 1)): z∈ shore o r:=by
 obtain ⟨v,x,y⟩:= march_visit o y 1 _ h; obtain ⟨g,c⟩:= Lattice.box_test.mp (lift_mem_box ((shoreq ..).mp p)); rw [shoreq,x,add_comm]; apply separation_box_add _ (Lattice.box_test.mpr ?_)
 constructor <;> intro i
 · have ht:= y.left i; change min (0:ℤ) _ ≤ _ at ht; specialize g i; change _ ≤ _ at g; omega
 have ht:=y.right i; change _ ≤ max (0:ℤ) _ at ht; specialize c i; omega

abbrev stipend (t:ℝ)(m:ℕ):ℝ:=4*(t*(1+(m:ℝ)))
-- variation quantity at radius m, t=tau, z=skyline
abbrev sceneDust (t z:ℝ)(m:ℕ):ℝ:=4*m*(stipend t m+z)
private def aim(g:Seat N→€)(o x:Seat N):€:=(g o)⁻¹*g x
lemma rootTint{p:BudgetPoint}{q:ℕ}{o:Seat N}{V:Pane N} (g:Pinwax p o q V): Nonempty (Pinwax p o q V) := ⟨g⟩ -- construct normalized
private def base(g : Seat N→€)(o:Seat N){p:BudgetPoint}{q:ℕ}{V:Pane N}(u:Pinwax p o q V)(h:u.color=g):Pinwax p o q V where
 color:=aim g o
 grip i w:= by
    change SU.group.chord ( ( (g o)⁻¹*g i.1)*V i*((g o)⁻¹*g (i.1+step i.2))⁻¹)≤_
    have e:((g o)⁻¹*g i.1)*V i*((g o)⁻¹*g (i.1+step i.2))⁻¹= (g o)⁻¹* (Lattice.gauge g V i)* ((g o)⁻¹)⁻¹:=by unfold Lattice.gauge; group
    rw [e,Gauge.chord_conj,←h]; exact u.grip i w
private lemma originV (o:Seat N){p:BudgetPoint}{q:ℕ}{V:Pane N}(u: Pinwax p o q V): (base u.color o u rfl).color o=1:= inv_mul_cancel _
private lemma travel_grip (o:Seat N){p:BudgetPoint}{q:ℕ}{V:Pane N}(u: Pinwax p o q V): Tiny (shore o q) (Lattice.gauge u.color V) (stipend p.threshold q):=by
 intro i h _; have v:= (shoreq o q i.1).mp h; exact (u.grip _ v).trans (by unfold stipend; gcongr; exact p.threshold_pos.le)
private lemma beacon (o:Seat N){p:BudgetPoint}{q:ℕ}{V:Pane N}{z:ℝ}(u: Pinwax p o q V) (h:u.color o=1)(s:Tiny (shore o q) V z)(i:Seat N)(w: i∈shore o q) (ℓ:0≤z): SU.group.chord (u.color i) ≤ sceneDust p.threshold z q:=by
 have t:= (shoreq o q i).mp w; let l' := march o i (1:Lattice.Order)
 let F:=u.color; let U:= Lattice.gauge F V
 have hu : travel U o l'=travel V o l'* (u.color i)⁻¹:= by rw [travel_gauge,arrive]; simp [F,h]
 have p₀(k:Seat N)(v:k∈ visits o l'):= coach q o i k w v
 have h': u.color i= (travel U o l')⁻¹* travel V o l':=by rw [hu]; group
 rw [h']; let dₗ(X:Pane N):= SU.group.chord (travel X o l'); have ht(X:Pane N)(z:ℝ)(g:0≤z)(p':Tiny (shore o q) X z): dₗ X≤4*q*z:= (Staff.held_peace N X _ l' _ p' p₀).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (Cube.march_len o i _ ((separation_comm ..).le.trans t): l'.length ≤ 4*q)) g)
 refine (SU.group.chord_triangle ..).trans ?_; rw [Gauge.chord_inv]; refine (add_le_add (ht U _ ?_ (travel_grip o u)) (ht V z ℓ s)).trans (Eq.le (mul_add ..).symm); unfold stipend; have v':=p.threshold_pos; positivity
-- p shadow

-- normalized exponent menus & actual consultations
variable {o:Seat N}{p:BudgetPoint}{V:Pane N}{q:ℕ}{z δ:ℝ} (g:Pinwax p o (q+1) V)(P:Parasols p δ (q+1))(D:Web SU.group)
local notation "t"=>p.threshold
abbrev treasury (w d:ℝ)(q:ℕ):ℝ := w*(8*(1+(q:ℝ)))/d
abbrev keynote (n:ℕ)(g:ℝ)(d:ℝ):ℝ:= d * treasury g d (n+1)
private def chalk : tangD N:= (baseL δ (q+1) g).2
include P g
lemma penRate :‖chalk (δ:=δ) g‖ ≤ treasury (t) δ (q+1):= (show ‖_‖ ≤ ‖baseL δ (q+1) g‖ from le_max_right ..).trans (base_length P (q+1) g le_rfl)
lemma touring (b:Edge (Seat N))(v:separation o b.1 ≤ q+1): increment 1 (δ • chalk (δ:=δ) g) b=Lattice.gauge g.color V b:= by
 change SU.group.lieExp _ * 1 = _; rw [mul_one]; exact lilt_record P g (q+1) _ v le_rfl
lemma course (x:Seat N)(i:PlaqAxes)(v:separation o x ≤ q): faceValue (increment 1 (δ • chalk (δ:=δ) g)) (x,i)=faceValue (Lattice.gauge g.color V) (x,i):=by
 let X':=increment (G:=SU.group) 1 (δ • chalk (δ:=δ) g); let Y':=Lattice.gauge g.color V
 have ht(j:Axis): separation o (x+step j) ≤ q+1:= (separation_triangle o x _).trans (Nat.add_le_add v (Work.E01.sep_step_le ..))
 have h(j m:Axis): X' (x,j)=Y' (x,j)∧ X' (x+step j,m)=Y' (x+step j,m):= ⟨touring g P _ (by omega : separation o x ≤ _), touring g P _ (ht _)⟩
 obtain ⟨⟨i,j⟩,_⟩:=i
 change faceValue X' _=faceValue Y' _
 unfold faceValue; simp only [square,travel,Step.neg_read,Step.pos_read,Step.vec_neg,Step.vec_pos,mul_one]
 rw [show x+step i+step j-step i=x+step j by abel, show x+step i+step j+ -step i - step j = x by abel, (h i j).1,(h i j).2,(h j i).1,(h j i).2]
#print axioms course
abbrev seamChord (ι:Web SU.group)(m:ℕ)(w e sag:ℝ):ℝ:=
 ι.scale* (keynote m w e)^2 + 2* SU.group.colorScale * sceneDust w sag (m+1)*w
open SliceRows
include D
def sleeves (p:BudgetPoint)(o:Seat N)(m:ℕ)(V:Pane N)(d:ℝ):Prop:=Tiny (shore o (m+1)) V d ∧ ∀ (x:Seat N)(a:PlaqAxes),separation o x ≤ m→ SU.group.chord (faceValue V (x,a)) ≤ p.threshold -- include unnecessary
lemma efficiency (v:g.color o=1)(slee:sleeves p o q V z)(sol:0≤z)
  (calm:keynote q p.threshold δ ≤ D.radius)
  (x:Seat N)(v':separation o x ≤ q)(j:PlaqAxes):
  ‖Boom.collar (δ • chalk (δ:=δ) g) (x,j) - SU.group.curvature (faceValue V (x,j))‖ ≤ seamChord D q p.threshold δ z:=by
 let f:= δ • chalk (δ:=δ) g
 have hV:=slee.2 x j v'; let d:=sceneDust (t) z (q+1)
 have he:=beacon o g v slee.1 x ((shoreq ..).mpr (v'.trans (by omega))) sol
 let I':= SU.group.curvature (faceValue V (x,j))
 let U:= Lattice.gauge g.color V
 let J:= SU.group.curvature (faceValue U (x,j))
 have e : ‖J-I'‖ ≤ 2* SU.group.colorScale * d * (t):=by
    unfold J U; rw [face_gauge,Gauge.curvature_conjugate]
    have t₂:= ((Next.Fluctuations.adjoint_norm_sub (g.color x) I'))
    exact t₂.trans (mul_le_mul (mul_le_mul_of_nonneg_left he (by have tδ:=SU.group.colorScale_pos; positivity)) ((SU.group.curvature_norm ..).trans hV) (norm_nonneg _) (by have hc:=((SU.group.chord_nonneg _).trans he); have hz:=SU.group.colorScale_pos; positivity))
 let k:= keynote q (t) δ
 have h:‖toLog f‖ ≤ k:=by rw [counted,norm_smul,Real.norm_of_nonneg P.pos.le];exact mul_le_mul_of_nonneg_left (penRate g P) P.pos.le
 refine (norm_sub_le_norm_sub_add_norm_sub _ J _).trans (add_le_add ?_ e)
 have a : faceValue (Precision.represent (toLog f)) (x,j)=faceValue U (x,j):=by rw [edits]; exact course g P _ _ v'
 have t':=D.defect (toLog f) (x,j) (h.trans calm)
 rw [a,curl_eq,norm_sub_rev] at t'; exact t'.trans (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h)|>.mpr h) (zero_le_one.trans D.cost))

lemma native_scaled (v:g.color o=1)(s:sleeves p o q V z)(sol:0≤z)
   (calm:keynote q p.threshold δ ≤ D.radius)(i:Postcard q):
   |δ*WakeRoad.native q o (chalk (δ:=δ) g) i - SU.group.curvature (faceValue V (Boom.port o i.1.1.val,i.1.2)) i.2| ≤ seamChord D q (t) δ z:=by
 let C:= Boom.port o i.1.1.val; let R:= (C,i.1.2)
 let f:= chalk (δ:=δ) g
 have h := efficiency g P D v s sol calm C (separation_box_add _ i.1.1.property) i.1.2
 have e: δ * WakeRoad.native q o f i= Boom.collar (δ • f) R i.2:= by
    change δ*(_-_ - (_-_) : ℝ)= δ*_ - δ*_ - (δ*_ - δ*_);ring
 rw [e]; exact (PiLp.norm_apply_le (p:=2) (Boom.collar (δ • f) R-SU.group.curvature (faceValue V R)) i.2).trans h
#print axioms native_scaled
-- Combined cost at origin
omit g P D
open Fock CF.Branch CF.Drapes
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {a c b E₀ e:ℝ}{u:Side}{k r:ℕ}{Z:Loom N}{F:Fob N e}
local notation "o*"=>bouton (0:Site N)
variable (X:Rialto 6 e δ b)(B:Plastron (0:Site N) u e (a/4) c F)(T:Tagbill a E₀ u k r p.B) (Q:Briefly p r e Z) (A:Arioso X B Q) (Y:Web SU.group)
local notation "h*"=>p.B/10
abbrev fault (m:ℕ)(o:Seat N)(U:Pane N) (i:Postcard m):ℝ:= SU.group.curvature (faceValue U (Boom.port o i.1.1.val,i.1.2)) i.2
abbrev tributeFog (Y:Web SU.group)(q:ℕ)(c a w δ z:ℝ)(u:Side):ℝ:=
 δ^2*(c*treasury w δ (q+1)^3)+ 2*(Lion u (a/4) c)*(w+seamChord Y q w δ z)*seamChord Y q w δ z
include Y X A T
lemma profit (P:Parasols p δ ((h*)+1))(calm:keynote (h*) p.threshold δ ≤ Y.radius) (j:2*((h*)+2)< (More N).val)(x:Orbit N) (v:pingS p.threshold (hoop (0:Site N) p.B) x.1)(d':Tiny (shore (o*) (h*+1)) x.1 z)(sol:0≤z):
 ‖δ^2 • (Matrix.trace (coinF Q B true x) - (musicA X B p) 0) - WakeRoad.Score (atoms X B p.B) (fault (h*) (o*) x.1)‖ ≤ tributeFog Y (h*) c a (t) δ z u:=by
 obtain ⟨g'⟩:=pinwaxes ((h*)+1) j
     (p:=p) (x:=(o*)) (U:=x.1) (CF.Vow.grow_b (Corona.halo_mono (show (h*)+1+1 ≤ p.B from by have := T.largeB;omega) le_rfl) v)
 let g:=base _ _ g' rfl
 let f := chalk (δ:=δ) g
 let W : Doub N:= (f,0)
 have v₁ : ‖W‖ ≤ treasury (t) δ (h*+1):=by rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]; exact penRate g P
 have p₁ := v₁.trans_lt (show treasury (t) δ (h*+1) < 1 from P.fine)
 have H:= A.hearsmall p₁ x v g.color (show Agrees _ (Gingham.Ruff.pencil δ W) (Lattice.gauge g.color x.1) from ?_)
 swap
 · intro i j _; have hp:= ((shoreq (o*) (h*) i.1).mp j).trans (show (h*) ≤ h*+1 from by omega)
   simp only [Gingham.Ruff.pencil,W,Pi.zero_apply,smul_zero,Gauge.mat_lieExp_zero,mul_one]; exact lilt_record P g (h*+1) _ hp le_rfl
 let U:=WakeRoad.native (h*) (o*) f; let V:=fault (h*) (o*) x.1; let discrepancy:= seamChord Y (h*) (t) δ z
 let t₁:=atoms X B p.B
 have cz:= WakeRoad.coin0 t₁
 have h₁:Tagbill (4*(a/4)) E₀ u k r p.B:=by rw [show (4:ℝ)*(a/4)=a from by ring]; exact T
 have hx:WakeRoad.coin t₁≤Lion u (a/4) c:=atoms_fee X B h₁
 have hv(x₀:Seat N)(l₀:PlaqAxes)(w:separation (o*) x₀≤h*): SU.group.chord (faceValue x.1 (x₀,l₀))≤ t:= (v (x₀,l₀) (not_disjoint_iff.mpr ⟨x₀,(shoreq ..).mpr (w.trans (by omega)), Work.E01.base_touched (x₀,l₀)⟩)).le
 have ht(i:Postcard (h*)): |V i|≤ t := (PiLp.norm_apply_le (p:=2) _ i.2).trans ((SU.group.curvature_norm _).trans (hv _ _ (separation_box_add _ i.1.1.property)))
 let ht'(i:Postcard (h*)):= native_scaled g P Y (originV _ _) ⟨d',hv⟩ sol calm i
 have b₀:=p.threshold_pos
 have hpos0: 0≤ discrepancy:=by unfold discrepancy seamChord sceneDust stipend; have vp:=P.pos; have vp':=SU.group.colorScale_pos;have vc:= zero_le_one.trans Y.cost; positivity
 let R:= p.threshold+discrepancy; have hp(i:Postcard (h*)):|(δ • U) i| ≤ R:=by have c0:= abs_sub_le (δ*U i) (V i) 0; rw [sub_zero,sub_zero] at c0; exact c0.trans (add_le_add (ht' i) (ht i) |>.trans_eq (add_comm ..))
 have hh:=score_equate t₁ (δ • U) V hp (fun i=>(ht i).trans (le_add_of_nonneg_right hpos0)) (b₀.le.trans (le_add_of_nonneg_right hpos0)) ht'
 refine (norm_sub_le_norm_sub_add_norm_sub _ (WakeRoad.Score t₁ (δ • U)) _).trans (add_le_add ?_ (hh.trans ?_))
 · rw [score_scale,← smul_sub,norm_smul,Real.norm_of_nonneg (sq_nonneg δ), show WakeRoad.Score t₁ U=_ from (jet_scores X B h₁ (by omega) P.pos f).symm] -- tune f shadow
   exact mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) v₁ _) (Shells.carrot_c B))) (sq_nonneg δ)
 · have hs:(0:ℝ)≤R:=by unfold R;positivity
   gcongr
