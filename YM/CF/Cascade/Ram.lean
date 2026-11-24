import YM.CF.Cascade.Esther
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
local notation "Z"=> coord (1:Axis)
abbrev Ail(n:Side):= Site (More n)→ℂ
def groan (P:ℂ→L[ℝ]ℝ):Ail n→ₗ[ℝ] Air n:= LinearMap.pi (R:=ℝ) fun i=> P.toLinearMap.comp (LinearMap.proj i)
def pill(n:Side)(x:Air n):form 1 (More n):=fun i=> if i.2=Z then x i.1 else 0
def pour(n:Side)(C: CoreX): Air n→L[ℝ] Cloud n:=(show Air n→ₗ[ℝ] Cloud n from
 { toFun:=fun x i=> pill n x i • C
   map_add':=fun x y=>by ext1 j; by_cases h:j.2=Z<;>simp [h,pill,add_smul]
   map_smul':=fun a b=>by ext1 i; by_cases h:i.2=Z <;>simp only [h,pill,ite_true,ite_false,Pi.smul_apply,smul_smul, smul_eq_mul,id_eq, RingHom.id_apply] <;> first| rfl | simp }) |>.toContinuousLinearMap
lemma quadR(n:Side)(x:Air n)(u:CoreX)(i): parts SU.group 1 (pour n u x) i=u i • pill n x:=by funext j; change (pour n u x j) i= _; change pill n x j * _= _; exact mul_comm ..
lemma climb {T:RG.StepData (More n) (More f)} (F:Forest T.ratio) (X: Matrix (Body 1 (More f)) (Body 1 (More n)) ℝ)(U0:Air f)(V:Air n) (U:CoreX) (p:X *ᵥ pill n V=pill f U0): let A:=Channel.rising F X (pour n U V); ∃ Q:Site (More f)→CoreX, collect SU.group A=collect SU.group (pour f U U0)+Font.pure Q:=by
 intro a
 let g:=pour n U V; let v:=pour f U U0; let T0:= straighten T F X
 let A(i): Body 0 (More f)→ℝ:= T0 *ᵥ parts group 1 g i
 let P(x:Site (More f)):CoreX:= WithLp.toLp 2 (fun i=> A i (x,vac)); refine ⟨P,?_⟩; funext i; ext1 j
 have hp: parts group 1 a j= X *ᵥ parts group 1 g j + d 0 (More f) *ᵥ A j := by rw [show parts _ _ a j= _ from Work.F04.parts_stretch F X g j,extracted, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
 have he:X *ᵥ parts group 1 g j = parts group 1 v j:= by unfold v g; rw [quadR,quadR,Matrix.mulVec_smul,p]
 rw [he] at hp
 rcases i with ⟨i,u⟩; have hy:=congr_fun hp (i,coord u); rw [Pi.add_apply,d_sites] at hy; exact hy
lemma zoneB {Y:Type*}[NormedAddCommGroup Y](x y:Site n)(v:Walk)(Q:Site n→Y)(W:Links (Per n) Y) (p:y=Lattice.stop x v): linkSum (W+ Font.pure Q) x v=linkSum W x v+ (Q y-Q x):=by
 subst y; induction v generalizing x with
 | nil=>simp [linkSum,Lattice.stop]
 | cons i w ih=>rw [linkSum,ih,linkSum,Lattice.stop]; congr 0; cases i with
   | mk u b => cases b<;> simp [Font.pure,Step.used, Step.vec, Step.read, sub_add_cancel] <;> abel
lemma fullB (V W:Cloud n)(Q:Site (More n)→CoreX)(i: Site (More n))(p:collect group V=collect group W+ Font.pure Q):fullG i V=fullG i W:=by
 funext a; unfold fullG; rw [p]
 rw [runoff, runoff,zoneB i i _ Q _ ((halts ..).symm), sub_self,add_zero]
lemma angSpan (P:Flight j t)(p:0<k)(r:4≤j)(s:4≤t)(w:(More f).val=(More n).val *P.L.val) (x:3≤(More n).val) (T:ℂ→L[ℝ]ℝ): let K:= P.visitRatio w; let A:= ∑ l: Site P.L,angel k P (port n) l • hike (n:=More f) (aliasAt (port n) l); installed K (Flight.duo k P).A0 *ᵥ pill n (groan T (hike (port n)))=pill f (groan T A) :=by
 intro K A; let Z':= port n; let B:=installed K (Flight.duo k P).A0
 have hp(Q:Momentum)(i:Body 1 (More n)):T (alto Q i)=pill n (groan T (hike Q)) i:=by unfold pill alto; split; rfl; exact map_zero _
 have hx : approached B *ᵥ alto Z'= ∑ l : Site P.L, angel k P Z' l • (alto (n:=More f) (aliasAt Z' l)) := by unfold Z'; rw [←mon0 x]; exact pines p r s P w _ (by rw [mon0 x]; simp [port,spark])
 funext ⟨i,j⟩; have hg: T ((approached B *ᵥ alto Z') (i,j))=(B *ᵥ pill n (groan T (hike Z'))) (i,j):=by
    unfold Matrix.mulVec dotProduct; rw [map_sum]; apply sum_congr rfl; intro i _; rw [← hp]; exact map_smul T _ _
 rw [show (installed K _ *ᵥ _) (i,j)= _ from hg.symm,hx, Finset.sum_apply]; by_cases h:j=coord 1
 · change T _ = if _ then _ else _; rw [if_pos h]; change T _= T _; congr 1; simp_rw [Pi.smul_apply,alto]; simp only [h,ite_true]; change _= A i; unfold A; rw [Finset.sum_apply]; rfl
 unfold A pill; simp_rw [Pi.smul_apply,alto]; simp [h]
end YM.CF.Cascade
