import YM.CF.Gloss.Net
import YM.CF.Reflect.Park
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable {A d D e:ℝ}{p:Part m B}
-- bridge rotations, enough for ports. validated extended ancestry only
open Phase.Sample RP
def phat(a:Trip m): Era m:=⟨Mir.glazed a.glare,a.move,false⟩
lemma blink(a:Trip m):ρx (phat a)= a.facesA:=by ext i:1; rfl
lemma ζ_b(a:Trip m)(U:Pack m B):vest B (phat a) U=Mir.Trip.onPack B a U:=by
 refine Prod.ext ?_ ?_
 · change flashA _ _= Trip.through B a U.1; rw [Skye.revoke]; change polarT false ∘ Lattice.pull (Mir.glazed a.glare) ((assembly _).embed ((rBar m B).embed a.move)) U.1=_; rw [show (assembly (CSide m B)).embed ((rBar m B).embed a.move)=_ from Trip.scale_eq m B a.move]; rfl
 funext v; exact Subtype.ext rfl -- possibly dove false rfl
lemma η_x(a:Trip m)(u:∀ i,a.glare i=false):wageZ (phat a)=false:=by
 unfold wageZ; change false.xor (detX (glazed a.glare))=_; rw [show a.glare=_ from funext u,glaze_one,det_i]; rfl
lemma η_d(m:Side)(i: Axis): wageZ (phat (slideM m i))=true:=by
 unfold wageZ; change false.xor (detX (glazed (fun j=>decide (i=j))))=_; rw [show glazed _= Signed.mirror i from ?_,det_t]; rfl
 unfold glazed Signed.mirror; congr! 2
lemma κo(x:Trip m):phat x⁻¹=(phat x)⁻¹:=by cases x; rfl
variable {W:Scroll m B p}(h: ScaleK A D W) (v:Budget B e d)
include h v
lemma brave(w:costG m B):ContinuousOn (billP W w) (payer m B e):=by
 exact (continuousOn_const (c:=rip m)).smul ((kilo_o _).comp_continuousOn ((gainS h v _).cont.comp (vest_p w.1).continuousOn (fun x p=>voxel B w.1 e x p))) -- tune
lemma soak(i:costG m B)(x y:Pack m B)(hx:x∈payer m B e)(hy:y∈payer m B e)(p:AgreeF (faces m (target i)) x.2 y.2)(hv:Agrees (room m B (target i)) x.1 y.1): billP W i x=billP W i y:=by
 unfold billP workQ; apply congrArg; apply congrArg; apply plates h v i.2 (voxel B _ e _ hx) (voxel B _ e _ hy)
 · intro j u; have he:(ρx i.1 j)∈ faces m (target i):= by unfold target; rw [←ϕ_p]; exact mem_image_of_mem _ u
   exact congrArg (doveV i.1.charge) (p _ he) -- tune
 exact setN i.1 _ _ _ ((ξ_p i.1 B _).symm ▸ hv)
variable(i:Axis)
def passQ {c:Part m B} (W:Scroll m B c)(i:Axis)(p:Pack m B):=∑ k:costG m B,bonus (target k) i • billP W k p
lemma pᵣ : ContinuousOn (passQ W i) (payer m B e):=continuousOn_finsetSum _ fun j _=> (continuousOn_const (c:=bonus (target j) i)).smul (brave h v j)
omit h v in
lemma vx (x:Pack m B) : cabinQ W x= passQ W i x+ star (passQ W i (Pbar m B i x)):=by
 unfold cabinQ passQ; let y:= slideM m i; let v:=phat y; have hv:v⁻¹=v:=by unfold v; rw [←κo,show y⁻¹=y from slide_inv ..]
 have hx(i:Index m): ρx v i= y.adv i:=rfl
 rw [←Equiv.sum_comp (eQ B v) (fun k=> bonus (target k) i • billP W k (Pbar m B i x)),star_sum, ←sum_add_distrib]; apply sum_congr rfl; intro j _; rw [show Pbar m B i x= vest B v x from (ζ_b ..).symm]; rw [show eQ B v j=mot v j from rfl,bill_s,star_smul,moot,hv,hx]; simp only [show ∀ z:ℂ,payZ v z=star z from fun z=> (by unfold payZ; rw [show wageZ v=true from η_d m i]; rfl),star_star,star_trivial,←add_smul]; rw [add_comm,show bonus (Trip.adv _ _) i+_=1 from bonusP i (target j),one_smul]
lemma pass_s (x y:Pack m B)(hx:x∈payer m B e)(hy:y∈payer m B e)(t:NorthOf m B i x y):passQ W i x=passQ W i y:=by
 apply sum_congr rfl; intro j _; by_cases p:target j∈ seaM m i; rw [soak h v j x y hx hy (t.labels.less (level_keep i p)) (fun e x y=> t.gaugeS e (plane_room i p x) (plane_room i p y))]; simp [bonus,p]
lemma pairt (x y z:Pack m B)(β:ℝ)(f:tiedK m B i x y z∈TallyR m B e β):cabinQ W (tiedK m B i x y z)=passQ W i (tiedK m B i x y y)+star (passQ W i (tiedK m B i x z z)):=by
 have he := (apt ..).mp f; have hg := tallyP f
 rw [vx i,sew i,pass_s h v i _ _ hg (tallyP he.1) (strum i x y z y), pass_s h v i _ _ (by rw [←sew]; exact Mir.Trip.dominated _ _ hg) (tallyP he.2) (strum i x z y z)]
end YM.CF.Gloss
