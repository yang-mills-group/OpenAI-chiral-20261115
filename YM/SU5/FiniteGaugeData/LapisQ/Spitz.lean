import YM.SU5.FiniteGaugeData.LapisQ.Kern
set_option autoImplicit false
set_option maxHeartbeats 540000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
set_option quotPrecheck false
namespace Vulcan
variable {n:Side}{G:Gauge} {F₀:Clip}{P:Bed}{u:Stage}{R:PathData G} {z:LogField G n}{ρ C Δ:ℝ}
local notation "V"=> Vault (Plush G (denim n))
local notation "M"=> P.metric.acts n
local notation "D"=> d 1 n
local notation "T"=> LogField G n
variable (F:Floor P u.clip n ρ C)(dp:0<ρ)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(a b:G.ColorIndex)
section unique
variable {α β:Type}[Fintype α][Fintype β](L:Matrix β α ℝ)
variable {B H K: Matrix β β ℝ}
def bentZ(x:β→ℝ):=∃ y:α→ℝ,L*ᵥ y=x
def exactZ (B:Matrix β β ℝ) (x y:β→ℝ) := bentZ L y∧∀ z,bentZ L z→ dotProduct z (B*ᵥ y)=dotProduct z x
private lemma symmetryB {β α:Type}[Fintype α][Fintype β] (L:Matrix β α ℝ) (x y): dotProduct x (L*ᵥ y)= dotProduct y (L.transpose *ᵥ x):=by rw [Matrix.mulVec_transpose,dotProduct_mulVec,dotProduct_comm y]
private lemma exclusive (p:∀ y:β→ℝ,y≠0→0<dotProduct y (B*ᵥ y)) {x y z:β→ℝ}(he:exactZ L B x y)(hv:exactZ L B x z): y=z:=by
 let v:=y-z; have hg: bentZ L v:=by obtain ⟨a,b⟩:= he.1; obtain ⟨a',b'⟩:= hv.1; exact ⟨a-a',by rw [mulVec_sub,b,b']⟩
 by_contra! e; refine not_le_of_gt (p v (sub_ne_zero_of_ne e)) (le_of_eq ?_); change dotProduct v (B*ᵥ (y-z))=_; rw [mulVec_sub,dotProduct_sub,he.2 v hg,hv.2 v hg,sub_self]
def Survey (B K:Matrix β β ℝ) := K.transpose=K ∧ (∀ x,bentZ L (K*ᵥ x)) ∧ (∀ x,bentZ L x→K *ᵥ (B*ᵥ x)=x)
lemma sun_owns (p:B.transpose=B)(z:Survey L B K) (x:β→ℝ): exactZ L B x (K*ᵥ x):=by
 refine ⟨z.2.1 x,fun y g=>?_⟩; rw [symmetryB, dotProduct_comm _ (B.transpose *ᵥ y), symmetryB K, p, z.1, z.2.2 y g,dotProduct_comm y] -- tune
lemma sun_unique (p:B.transpose=B)(h:∀ y: β→ℝ,y≠0→0<dotProduct y (B*ᵥ y)) (z:Survey L B K) (v:Survey L B H):K=H:= Matrix.ext_iff_mulVec.mpr (fun a=>exclusive L h (sun_owns L p z a) (sun_owns L p v a)) -- tune
lemma sun_rays (z:Survey L B K)(dp:0<ρ)(P:∀ y:β→ℝ,ρ*dotProduct y y≤dotProduct y (B*ᵥ y))(hp:B.transpose=B) (x:β→ℝ): let y:=K*ᵥ x; ρ^2*dotProduct y y≤ dotProduct x x:=by
 intro y; have he:= sun_owns L hp z x; have hw := P y; have ht: dotProduct y (B*ᵥ y)=dotProduct y x:=he.2 y he.1; rw [ht] at hw
 have hx:0≤dotProduct (ρ • y-x) (ρ • y-x):= flourish ..; simp_rw [dotProduct_sub,sub_dotProduct,smul_dotProduct,dotProduct_smul,smul_eq_mul, dotProduct_comm x y] at hx; nlinarith only [hx, mul_le_mul_of_nonneg_left hw dp.le]
end unique
include W A
lemma sunM : Survey (d 1 n) (P.metric.acts n) (sineB F dp a a):= by
 refine ⟨sineB_sym F dp a a,fun i=>?_ , fun i hi=>?_⟩
 · rw [peaking]; exact ⟨_,(show _ from Eq.refl (beams F dp a _))⟩ -- infer hole
 obtain ⟨i,rfl⟩:=hi; rw [return_π F dp W A,if_pos rfl]
omit W A in
include F dp in
lemma prismatic(x:form 2 n)(e:x≠0):0<dotProduct x (P.metric.acts n*ᵥ x):= (mul_pos dp (flourish_p x e)).trans_le (F.uniform.1 _).1
lemma pigment : sineB F dp a a=sineB F dp b b:=sun_unique (d 1 n) F.symmetric.1 (prismatic F dp) (sunM F dp W A a) (sunM F dp W A b)
lemma abyss (p:a≠b): sineB F dp a b=0:=by
 refine Matrix.ext_iff_mulVec.mpr ?_; intro x
 rw [Matrix.zero_mulVec]; let Vq:= sineB F dp a b; let Q:= Vq*ᵥ x; by_contra! e
 have h:bentZ (d 1 n) Q:=by change bentZ (d 1 n) (sineB F dp a b*ᵥ _); rw [peaking]; exact ⟨_,(show _ from Eq.refl (beams F dp a _))⟩
 obtain ⟨z,b'⟩:=h; have he:sineB F dp b a*ᵥ (M*ᵥ Q)=0:=by rw [←b',return_π F dp W A, if_neg p.symm] -- local M
 have ht:= prismatic F dp Q e; have hZ:dotProduct Q (M*ᵥ Q)=0:=by rw [dotProduct_comm]; change dotProduct (M*ᵥ Q) (sineB F dp a b*ᵥ x)=_; rw [symmetryB, sineB_sym,he,dotProduct_zero]
 exact ne_of_gt ht hZ
-- stationary structure
variable {α β:Type}[Fintype α][Fintype β]
abbrev Rotor (s:Site n)(α:Type): Equiv.Perm (Site n × α):= (Equiv.addRight s).prodCongr (Equiv.refl _)
local notation "L" a:max=> Rotor s a
abbrev Sturn (s:Site n) (A: Matrix (Site n ×α) (Site n×β) ℝ) := A.submatrix (Rotor s α) (Rotor s β)
def stationaryB (A: Matrix (Site n×α) (Site n×β) ℝ):=∀ s:Site n,Sturn s A=A
variable (s: Site n)
omit W A F in
lemma radialB (P: Bloch.Row α β): stationaryB (n:=n) (P.acts n):=by
 intro s; ext ⟨o,i⟩ ⟨k,j⟩; change (∑' x:Cover, if k+s=o+s+wrap n x then P i j x else 0)=_; unfold Row.acts; simp_rw [add_right_comm o s, add_left_inj]; rfl
omit W A F in
private lemma radish (P: Matrix (Site n×α) (Site n×β) ℝ)(x:Site n×β→ℝ) : Sturn s P *ᵥ (x ∘ Rotor s β) = (P*ᵥ x) ∘ Rotor s α:=by
 ext ⟨i,j⟩; exact Equiv.sum_comp (Rotor s β) (fun j'=> P (Rotor s α (i,j)) j'*x j') -- tune extent
omit W A F in
private lemma radialL(P: Matrix (Site n×α) (Site n×β) ℝ)(x:Site n×β→ℝ) (hv:stationaryB P): P*ᵥ (x ∘ Rotor s β)=(P*ᵥ x) ∘ Rotor s α := Eq.trans (congrArg (· *ᵥ (x ∘ Rotor s β)) (hv s).symm) (radish s P x)
omit W A F in
private lemma radish_r (x:form 2 n):∃ y:form 2 n,x=y ∘ Rotor s (TypeFace 2):= ⟨x ∘ (Rotor s (TypeFace 2)).symm, (by funext i; exact congrArg x (Equiv.symm_apply_apply _ i).symm)⟩
omit W A F in
private lemma swivel(x:form 2 n) :bentZ (d 1 n) x ↔ bentZ (d 1 n) (x ∘ Rotor s (TypeFace 2)):=by
 let o:= Rotor s (TypeFace 1); let o':= Rotor s (TypeFace 2)
 refine ⟨fun p=>?_,fun p=>?_⟩; · obtain ⟨_,rfl⟩:=p; exact ⟨_, radialL s (d 1 n) _ (radialB (cobound 1))⟩
 obtain ⟨b,v⟩:= p; refine ⟨b∘o.symm,?_⟩; let y:=D*ᵥ (b∘o.symm); have he:=radialL s (d 1 n) (b ∘ o.symm) (radialB (cobound 1)); rw [show ((b∘o.symm) ∘ Rotor s (TypeFace 1))=b from (by funext i; exact congrArg b (Equiv.symm_apply_apply o i)),v] at he; exact o'.surjective.right_cancellable.mp he.symm -- tune right comp
omit W A F in
private lemma rotB (B: Matrix (Body 2 n) (Body 2 n) ℝ)(h: Survey (d 1 n) (P.metric.acts n) B) : Survey (d 1 n) (P.metric.acts n) (Sturn s B):=by
 refine ⟨Eq.trans (show (Sturn s B).transpose= Sturn s B.transpose from rfl) (congrArg (fun A=> Sturn s A) h.1),fun i=> ?_ ,fun i hi=>?_⟩ -- rfl transpose?
 · obtain ⟨x,v⟩:= radish_r s i; rw [v,radish]; exact (swivel s _).mp (h.2.1 _)
 obtain ⟨x,v⟩:= radish_r s i; rw [v,radialL s (P.metric.acts n) x (radialB P.metric),radish, h.2.2 x ((swivel s x).mpr (v ▸ hi))]
lemma splend : stationaryB (sineB F dp a a):= fun s=> sun_unique (d 1 n) F.symmetric.1 (prismatic F dp) (rotB s _ (sunM F dp W A a)) (sunM F dp W A a)
end Vulcan
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Vulcan.abyss
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Vulcan.splend
