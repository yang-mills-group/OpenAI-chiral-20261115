import YM.CF.Mir.Border

/-! Permute the fermion grid, arbitrary single reflection moves positive to holes. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {N m B : Side}
def motion (s : Signed) (v : Site N) : Equiv.Perm (Site N) where
  toFun x := affine s v x
  invFun x := s⁻¹.act (x-v)
  left_inv x := by simp [affine]
  right_inv x := by simp [affine]
def siteM (e : Equiv.Perm (Site N)) : UNI (Model N) := ⟨jump e (fun _=>1),jump_unitary _ _ fun _=>one_mem _⟩
lemma siteSpin (e : Equiv.Perm (Site N)) (A) : twist (siteM e) (spin N Slot A)=spin N Slot A := by
  apply twist_comm; simp only [siteM,spin,jump_mul,Equiv.trans_refl,Equiv.refl_trans,one_mul,mul_one]
lemma cc_site (e : Equiv.Perm (Site N)) : ccU (siteM e)=siteM e := by apply Subtype.ext; simp [ccU,siteM,jump_cc]
lemma siteField (e : Equiv.Perm (Site N)) (x) : congrC (siteM e) (Cfield x)=Cfield (x ∘ ⇑e) := by
  rw [congr_form,cc_site,← twist_formula]; apply twist_comm; simp only [siteM,Cfield,jump_mul,Equiv.trans_refl,Equiv.refl_trans,Function.comp_apply,one_mul,mul_one]

namespace Trip
-- elementary glare has no permutation; spacing relation

def gaugeR (m B : Side) : Ratio (More m) (CSide m B) := ⟨B,rfl⟩
lemma scale_eq (m B) (x : Site (More m)) : (assembly (CSide m B)).root ((gaugeR m B).root x)=(scaleR m B).root ((assembly (More m)).root x) := by
  rw [show x=wrap _ (lift x) from (wrap_lift x).symm]
  simp only [Ratio.root_embed, Ratio.embed_wrap, ← map_nsmul]
  -- combine
  congr 1; exact smul_comm ..
-- correction to put each reflected odd image at fermion center.
def ankle (p : Axis→Bool) : Site N := fun i=> if p i then -1 else 0
lemma foot (p : Axis→Bool) : (assembly N).root (ankle p)+1=(glazed p).act 1 := by
  let x : Cover := fun i=> if p i then -1 else 0
  rw [show ankle (N:=N) p=wrap N x by
    funext i; cases l:p i <;> simp [ankle,x,l,wrap_here], Ratio.root_embed, Ratio.embed_wrap]
  funext i; change wrap _ ((assembly _).count.val • x) i+1=_
  change wrap (More N) (2 • x) i+1= _; rw [wrap_here,glaz]; cases l:p i <;> simp [x,l]; ring -- tune

def fermShift (m B : Side) (a : Trip m) := (gaugeR m B).root a.move+ankle a.glare
def fperm (m B : Side) (a : Trip m) := motion (glazed a.glare) (fermShift m B a)
variable (b : Trip m) (B)
lemma track (x) : node (fperm m B b x)=run B b (node x) := by
  change (assembly _).root ((glazed b.glare).act x+_)+_=_; rw [map_add,fermShift,map_add, scale_eq]; unfold run torShift; simp only [node,affine, Signed.act_add];
  rw [←foot,show (assembly (CSide m B)).root ((glazed b.glare).act x)= (glazed b.glare).act ((assembly _).root x) from Ratio.signed ..]; unfold paneShift; abel
lemma double_pull (U : Skin m B) : links (through B b U)=Lattice.pull (glazed b.glare) (fermShift m B b) (links U) := by
  funext ⟨x,i⟩; let p := (posDir i).rotate (glazed b.glare)
  have hm : links (through B b U) (x,i)=travel (links (through B b U)) x [posDir i] := by simp [travel]
  rw [hm,deep,through,travel_pull]; change travel U (run B b (node x)) [p,p] = p.read _ _
  have H := deep U (fperm m B b x) [p]
  change p.read (links U) _*1=travel U (node _) [p,p] at H; rw [track,mul_one] at H; exact H.symm
lemma played (U : Skin m B) (s q) : grain m B (through B b U) (riseF b s) q=grain m B U s q ∘ fperm m B b := by funext y; unfold grain; simp [fees_eq,track]

-- reflected cut d in fermion grid so signs match old c: tangent shift = c-w, normal -c+w-1

def far (c : Phase.Part m B) : Phase.Part m B := fun i=> if b.glare i then fermShift m B b i-1-c i else c i-fermShift m B b i -- ambiguous Part
lemma tram (U : Skin m B) (c : Phase.Part m B) (i : Axis) :
    twist (siteM (fperm m B b)) (shift matter (links U) c i) = if b.glare i then star (shift matter (links (through B b U)) (far B b c) i) else shift matter (links (through B b U)) (far B b c) i := by
  let V := siteM (fperm m B b); let J := fperm m B b; let L := links U; let P := links (through B b U); let d := far B b c; let t := fermShift m B b
  have hc (x) : J x i=(if b.glare i then -(x i) else x i)+t i := by change (glazed _).act _ i+t i=_; rw [glaz]
  have hi (x : Site (CSide m B)) : J (x+step i)= J x+(if b.glare i then -step i else step i) := by
    change affine (glazed b.glare) t (x+step i)=affine (glazed b.glare) t x+_; unfold affine; rw [Signed.act_add]; have he : (glazed b.glare).act (step i : Site (CSide m B))=(if b.glare i then -step i else step i) := by funext j; cases l:b.glare i <;> by_cases g:j=i <;> simp_all [glaz]
    rw [he]; abel
  have hz (x : Phase.Part m B) : P (x,i)=if b.glare i then (L (J x-step i,i))⁻¹ else L (J x,i) := by -- tune
    unfold P; rw [double_pull]; change Step.read (Step.rotate ..) _ _ = _; unfold Step.read Step.rotate Step.used glazed posDir; cases l:b.glare i <;> simp [l]; rfl; rfl
  change twist V _ = if b.glare i then star (shift matter P d i) else shift matter P d i
  cases l:b.glare i
  · simp only [Bool.false_eq_true,ite_false]; apply twist_comm
    simp only [V,siteM,shift,jump_mul];
    have he : J.trans (advance i)=(advance i).trans J := by
      ext x : 1; change J x+step i = J (x+step i); rw [hi,l,if_neg (by decide)]
    rw [show (fperm m B b).trans (advance i) = _ from he]; apply congrArg; funext x; simp only [mul_one, one_mul]; change hop matter L c i (J x)=hop matter P d i x
    rw [hop,hop,hz,l,if_neg (by decide)]; unfold seam; rw [hc,l];
    have hm : x i+t i=c i ↔ x i=d i := by unfold d far; rw [l,if_neg (by decide)]; exact eq_sub_iff_add_eq.symm
    simp only [Bool.false_eq_true,ite_false,hm]
  rw [if_pos rfl]; apply twist_comm; simp only [V,siteM,shift,jump_star,jump_mul]
  have hg (x) : J x=J ((advance i).symm x)-step i := by
    let a : Phase.Part m B := (advance i).symm x; have hk : a+step i=x := (advance i).apply_symm_apply x
    nth_rw 1 [←hk,hi,if_pos l]; exact (sub_eq_add_neg _ _).symm
  have he : J.trans (advance i)=(advance i).symm.trans J := by ext x : 1; change J x+step i= J ((advance i).symm x); conv_lhs => rw [hg x]; rw [sub_add_cancel]
  rw [show (fperm m B b).trans (advance i)=_ from he]; apply congrArg; funext x; simp only [one_mul,mul_one]; change hop matter L c i (J x)=star (hop matter P d i ((advance i).symm x))
  let y : Phase.Part m B := (advance i).symm x
  change _=star (hop matter P d i y); rw [hop,hop, hz,l,if_pos rfl,←show J x=J y-step i from hg x,color_inv,star_smul,star_star,seam_real]
  have ht : J x i=c i ↔ y i=d i := by
    rw [show J x i= J y i-(step i) i from congr_fun (hg x) i,hc,l,if_pos rfl,step_apply, if_pos rfl]; unfold d far; rw [l,if_pos rfl];
    change -(y i)+t i-1=c i↔y i=t i-1-c i; constructor <;> intro h
    · rw [←h]; abel
    rw [h]; abel
  unfold seam; simp only [ht]
end Trip
end YM.CF.Mir
