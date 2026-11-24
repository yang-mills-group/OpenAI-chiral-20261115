import YM.SU5.LitCurrent.Saw
import YM.SU5.LitCurrent.Transport
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Salt
abbrev Ensemble (N:Side):= Site N × FaceDir
def teamTravel (s:Sweep N)(i:Ensemble N): Ensemble N:= (pose s i.1,faceAt s i.2)
lemma team_mul (s t:Sweep N): teamTravel t ∘ teamTravel s=teamTravel (s*t):=by
 funext i; simp only [teamTravel,Function.comp_apply,pose_mul,face_at_mul]
lemma location_mul (s t:Sweep N): pose t ∘ pose s=pose (s*t):=funext (pose_mul s t)
private lemma real_Star (s:Sweep N)(z:Bool)(A:Op I)(p:IsSelfAdjoint A):IsSelfAdjoint (realR s z A):=by
 have he:star (ech s A)=ech s A:=by rw [←echo_star,p]
 cases z
 · change star (if det_S s then star (ech s A) else ech s A)=(if det_S s then star (ech s A) else ech s A)
   simp only [he,ite_self]
 change star (Thera.jazz (det_S s) (ech s A))=Thera.jazz (det_S s) (ech s A)
 cases h:det_S s <;>simp only [Thera.jazz, Bool.false_eq_true,ite_false,ite_true,star_neg,he]
private lemma real_neg (s:Sweep N)(z:Bool)(A:Op I):realR s z (-A)= -realR s z A:=by
 cases z <;>cases t:detX s.s<;>simp [realR,Sour.bolt,foeL,Sault.hitL,Sault.doveL,Thera.jazz,t]

abbrev vectorTree (L:Axis→Site N→ StageTree N d a v)(i: Ensemble N):StageTree N d a v:=if i.2.2 then (StageTree.lose (L i.2.1 i.1)) else L i.2.1 i.1
variable {L:Axis→Site N→ StageTree N d a v}
lemma vector_flip (L:Axis→Site N→ StageTree N d a v)(x:Site N)(e:FaceDir)(S:Sa N)(y):
    (vectorTree L (x,axisFlip e)).F S () y= - (vectorTree L (x,e)).F S () y:=by
 unfold vectorTree; cases e with |mk i b=> cases b; exact rfl; simp [axisFlip,StageTree.lose] -- case indent
lemma halo_flip (L:Axis→Site N→ StageTree N d a v)(x:Site N)(e:FaceDir)(S:Sa N)(U:Pane N)(y:Openc (More N) d)(t:y.val=profile U):
    (haloB (vectorTree L) teamTravel false (x,axisFlip e)).F S () y=
    -((haloB (vectorTree L) teamTravel false (x,e)).F S () y):=by
 rw [StageTree.tree_proj _ _ _ U y t, StageTree.tree_proj _ _ _ U y t]
 have he(s:Sweep N): teamTravel s (x,axisFlip e)=(pose s x,axisFlip (faceAt s e)):=congrArg _ (face_at_flip s e) -- tune infer
 simp_rw [he,vector_flip,real_neg,sum_neg_distrib,smul_neg]; rfl

abbrev bears (J:Site N→ FaceDir→Op (Single N))(r:ℕ)(x:Site N):Op I:=∑ e:FaceDir,J (destSite x r e) e
lemma curl_permit (J:Site N→ FaceDir→Op (Single N))(p:∀ x e,J x (axisFlip e)= -J x e)(r:ℕ)(x:Site N):
    bears J r x=∑ i:Axis,(J (x+r • step i) (i,false)-J (x-r • step i) (i,false)):=by
 unfold bears; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [Fintype.sum_bool, show (i,true)=axisFlip (i,false) from rfl, p]
 simp [destSite,axisFlip,strideD,Step.vec,sub_eq_add_neg]; abel -- tune occurrence

/-- Full synchronized ledger. `chart` gives determinant character before assembly,
 even axes crossing charge. Body equality only at Guard uses. This work keeps both
 carrier/quadratic price and location transports before regulator take. -/
structure Pattern (P T:SOp N)(r:ℕ)(d a B:ℝ) where
    A : Site N→StageTree N d (4*a) B
    J : Ensemble N→ StageTree N d (4*a) B
    moorA : ∀ x, moored (node x) (A x)
    moorJ : ∀ i:Ensemble N, moored (node i.1) (J i)
    tax (x:Site N)(U:Pane N)(u:Guard U d)(y:Openc (More N) d)(t:y.val=profile U): taxKernel P x r y.val=sky (A x) y
    chart (s:Sweep N)(x:Site N)(S:Sa N)(U:Pane N)(y:Openc (More N) d)(t:y.val=profile U): (A (pose s x)).F (actY s S) () (Sour.fog s d y) = realR s true ((A x).F S () y)
    herm (x:Site N)(S:Sa N)(U:Pane N)(y:Openc (More N) d)(t:y.val=profile U):IsSelfAdjoint ((A x).F S () y)
    chimeJ (x:Site N)(U:Pane N)(u:Guard U d)(y:Openc (More N) d)(t:y.val=profile U):
        bears (fun x e=>sky (J (x,e)) y) r x=Sault.inward (P y.val) (roomW x r) (T y.val)
    chartJ (s:Sweep N)(i:Ensemble N)(S:Sa N)(U:Pane N)(y:Openc (More N) d)(t:y.val=profile U): (J (teamTravel s i)).F (actY s S) () (Sour.fog s d y) = realR s false ((J i).F S () y)
    revJ (x:Site N)(e:FaceDir)(S:Sa N)(U:Pane N)(y:Openc (More N) d)(t:y.val=profile U):
       (J (x,axisFlip e)).F S () y= -(J (x,e)).F S () y

private lemma dive_turn {P T:SOp N}(p:Permission P T d)(r:ℕ)(A:Ensemble N→ StageTree N d a v)
    (h:∀ (x:Site N)(U:Pane N),Guard U d→∀ y:Openc (More N) d,y.val=profile U→
       bears (fun x e=>sky (A (x,e)) y) r x=Sault.inward (P y.val) (roomW x r) (T y.val))
    (x:Site N)(U:Pane N)(u:Guard U d)(y:Openc (More N) d)(t:y.val=profile U):
    bears (fun x e=>sky (haloB A teamTravel false (x,e)) y) r x=Sault.inward (P y.val) (roomW x r) (T y.val):=by
 let D:=Sault.inward (P (profile U)) (roomW x r) (T (profile U)); unfold bears
 simp_rw [StageTree.frame_proj A _ _ U y t,←smul_sum]; rw [sum_comm]
 have he(s:Sweep N): (∑ d':FaceDir, realR s⁻¹ false (sky (A (teamTravel s (destSite x r d',d'))) (Sour.fog s d y)))=D:=by
    rw [←real_f]
    let W(d':FaceDir) := sky (A (destSite (pose s x) r d',d')) (Sour.fog s d y)
    have hx (d'):sky (A (teamTravel s (destSite x r d',d'))) (Sour.fog s d y)= W (bearings s d'):=by unfold W; rw [teamTravel,pose_hop]; rfl
    rw [sum_congr rfl (fun a _=>hx a), Equiv.sum_comp]; unfold W
    let v:=Sour.fog s d y; let f:= real_box s d U y t; rw [show (∑ e:FaceDir,_)=_ from h (pose s x) (flashA s U) (share s U u) v f, show v.val=_ from f, ←p.inward_move u s x, vale_d, mul_inv_cancel]; exact real_i ..
 simp_rw [he,t,sum_const,card_univ,avg_s]; rfl
lemma boltages {P T:SOp N}(r:ℕ)(p:Permission P T d)
    (pa:∀ x, Soak (node x) (taxKernel P x r) (4*a) v d)
    (pj:∀ j x, Soak (node x) (firstLink P T r j x) (4*a) v d): Nonempty (Pattern P T r d a (Tenant.quota^2*v)):=by
 choose L u l using fun x=> issue (pa x)
 choose M q k using fun i x=> issue (pj i x)
 let A (x:Site N): StageTree N d (4*a) v:= (L x).repair
 let J:= vectorTree M
 have tA:∀ i:Site N,NearL (A i) (fun _:Unit=>taxKernel P i r):=by
    rintro i ⟨⟩ y V h t; change taxKernel _ _ _ _ = sky (A i) y; rw [l]; exact (StageTree.mendSky (L i) V y t (by rw [←l i y,t]; exact p.tax_self h i)).symm
 refine ⟨⟨haloB A pose true,haloB J teamTravel false,?_,?_,fun x U g y t=> ?_,fun s x S U y t=>?_ ,fun x S U y t=>?_ , dive_turn p r J ?_ ,fun s x S U y t=>?_,fun x =>halo_flip M x⟩⟩
 · intro x; refine StageTree.moor_frame A _ x (fun s=>?_) true; rw [←pose_node]; exact StageTree.mend_moor _ (u _)
 · rintro ⟨x,e⟩; refine StageTree.moor_frame J _ (x,e) (fun s=> ?_) false; change moored ((boxA s).symm (node x)) (J (pose s x,faceAt s e)); rw [←pose_node]; unfold J vectorTree; split <;> exact q _ _
 · exact hush_t A _ pose true tA (fun s _ _ a i=>(p.tax_move a s i).symm) x () y U g t -- tune
 · exact flash_P s A pose true location_mul x () _ y t S
 · rw [StageTree.tree_proj A pose x U y t]; unfold IsSelfAdjoint; rw [star_smul,star_sum, show star (avg N:ℂ)=(avg N:ℂ) from by simp]; refine congrArg _ (sum_congr rfl fun s _=>?_)
   exact real_Star s⁻¹ true _ (StageTree.repair_self (L _) (flashA s U) _ (real_box s _ _ _ t) _)
 · intro x U u' z t; rw [curl_permit (p:=?_)] -- syntax
   · have ht:=first_sum P T r z.val (show IsStarProjection _ from t.symm ▸ p.projection U u') x
     exact (Finset.sum_congr rfl (fun i _=>congrArg₂ (·-·) (k i _ z).symm (k i _ z).symm)).trans ht.symm
   · intro x e; unfold sky J; simp_rw [vector_flip,sum_neg_distrib]
 exact flash_P s J teamTravel false team_mul x () _ y t S

lemma plan_code (r:ℕ)(h:0<a)(p:0<b)(d:ℝ):∃ B> (0:ℝ), ∀ {N:Side} (P T:SOp N),
    Solo (100*(4*a)) b P d → Solo (100*(4*a)) b T d → Permission P T d→ Nonempty (Pattern P T r d a B):=by
 obtain ⟨Z,hZ,w⟩:= first_bill (d:=d) r (show 0<4*a by positivity) p
 let v := max Z (taxPrice (4*a) b r); have hx:= hZ.trans_le (show Z ≤ v from le_max_left ..); have ht:0<Tenant.quota:= (show (0:ℝ)<16 by norm_num).trans_le quota_bound
 refine ⟨Tenant.quota^2*v, by positivity, fun P T Q K Y=>?_⟩
 exact boltages r Y (fun x=> lift_U (tax_bill P x (show 0≤4*a by positivity) (Q.drop (by linarith)) r) (le_max_right ..)) (fun i x=> lift_U (w P T Q K i x) (le_max_left ..))
end YM.CF.LitCurrent
