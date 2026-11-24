import YM.CF.BProof.Charge.TaylorPrice
import YM.CF.BProof.Angular.Climate

/-! L and Q specialize via `roll`. Linear in Lie slots at any severity, copying both
N halfs from own face angular columns after gap fixing. Zero values on D bands and on
normal links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Charge Charge.Form
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side}(Y:Yard s)(i:Y.Index)(x:Per s)(p:Space s)(n:TAxis)

abbrev Branch := Y.Door → Lie
def lastDepth : Fin Y.short:=⟨Y.short-1, Nat.sub_lt Y.short_pos (by decide)⟩
lemma last_depth : Y.lastDepth.val+1=Y.short:=by have := Y.short_pos; change Y.short-1+1=Y.short; omega
/-- compute where gap data is fetched; support certificate. -/
def project (r:Y.Index)(d:ℕ) : Option Y.Door:= if h:d=0 ∨ Y.short<d then none else some ((r,p),(⟨d-1,by omega⟩,n))
lemma projd (d:Fin Y.short): project Y p n i (d.val+1)=some ((i,p),d,n):=by unfold project; split; rename_i H; have := d.isLt; omega; congr
@[simp] lemma projs : project Y p n i Y.short=some ((i,p),Y.lastDepth,n):= by conv_lhs=> rw [← Y.last_depth]; exact Y.projd i p n _ -- arg order?
@[simp] lemma proj0 : project Y p n i 0=none:=dif_pos (by simp)

def delegate (i:Y.Index) := if Y.D i then none else project Y p n (Y.location i (flag (Y.u i) x Y.long)) Y.short
def consult (i:Y.Index) := project Y p n i (Y.depth i x)
def find (x:Per s)(p:Space s)(n:TAxis): Option Y.Door := if Y.Band (Y.twinsBand x) x then delegate Y x p n (Y.twinsBand x) else consult Y x p n (Y.twinsGap x)
def heir (b:Bond s): Option Y.Door:= Fin.cases none (Y.find (time b.1) (space b.1)) b.2
@[simp] lemma heir_v : Y.heir (vert x p)=none:=rfl
@[simp] lemma heir_h : Y.heir (horiz x p n)=Y.find x p n:=by simp only [heir,horiz,time_join,space_join,Fin.cases_succ]
lemma find_band (h:Y.Band i x): Y.find x p n= delegate Y x p n i:=by rw [find,Y.u_part _ _ h,if_pos h]
lemma find_gap (h:Y.Gap i x): Y.find x p n=consult Y x p n i:=by
 unfold find; split; swap; next H=> rw [Y.v_part _ _ h]
 next H=>
  generalize Y.twinsBand x = j at *; rcases Y.common j x H h with ⟨r,u⟩|⟨r,u⟩ <;> subst j <;> subst x
  · have ht: flag (Y.u (i+1)) (Y.u (i+1)) Y.long=false:=(by simp); unfold delegate consult; simp only [next,ite_not,depth, v_in,Nat.sub_self]; split; rw [ht]; simp [location]; exact (Y.proj0 i p n).symm
  have ht: flag (Y.u i) (Y.v i) Y.long=true:= (flag_true ..).2 (by rw [u_in]; exact cut_lt _ Y.long_pos); unfold delegate consult; simp only [depth,along_self,Nat.sub_zero]; split; exact (Y.proj0 i p n).symm; rfl
lemma locate {r:ℕ}(h:Y.Vic i r x)(hv:4*r<Y.long){d:Y.Door}(e:Y.find x p n=some d): d.1=(i,p):=by
 rcases Y.vic_split i r x (by omega) h with h|h|h
 · rw [find_band Y _ x p n h.2,delegate] at e; split at e; contradiction; rw [(Y.cold_flag i x hv h).1,projs,Option.some.injEq] at e; rw [← e]; rfl
 · rw [find_gap Y i x p n h,consult, project] at e; split at e; contradiction; exact congrArg Prod.fst (Option.some.inj e).symm
 rw [find_band Y _ x p n h.2,delegate] at e; split at e; contradiction; rw [(Y.hot_flag _ x hv h).1,projs,Option.some.injEq] at e; rw [←e]; simp [location]
lemma consults (d:ℕ)(h:d≤Y.short) : consult Y (Y.atD i d) p n i= project Y p n i d := congrArg (project Y p n i) (Y.depth_at i h)
lemma gap_find (d:ℕ)(h:d≤Y.short) : Y.find (Y.atD i d) p n=project Y p n i d:= (Y.find_gap i _ _ _ (Y.atD_mem i h)).trans (Y.consults i p n d h)
lemma inter_heir (b:Y.Door) : Y.heir (Y.inter b)=some b:=by unfold inter; rw [heir_h, reach, gap_find Y _ _ _ _ b.2.1.isLt,projd]

def spec (d:Option Y.Door) : Y.Branch→ₗ[ℝ] Lie:= d.elim 0 fun i=>LinearMap.proj i
def roll : Y.Branch→ₗ[ℝ] Form.Argument s:= LinearMap.pi (fun i=> Y.spec (Y.heir i))
lemma roll_c (W:Y.Branch)(i:Bond s) : roll Y W i= Y.spec (Y.heir i) W:=rfl
@[simp] lemma roll_v (W:Y.Branch): roll Y W (vert x p)=0:=by rw [roll_c,heir_v]; rfl
@[simp] lemma roll_inter (W:Y.Branch)(b:Y.Door) : Y.roll W (Y.inter b)=W b:=by rw [roll_c,inter_heir]; exact rfl
lemma roll_h (W:Y.Branch)(h:Y.Gap i x): Y.roll W (horiz x p n)=Y.spec (consult Y x p n i) W:=by rw [roll_c,heir_h,find_gap Y i _ p n h]
def roof (Z:Finset Y.Col) (W:Y.Branch): Y.Branch:= fun i=> if i.1∈Z then 0 else W i
lemma roll_roof (Z: Finset Y.Col) (W:Y.Branch) {r:ℕ}(h:Y.Vic i r x)(hv:4*r<Y.long)(u:(i,p)∉ Z): Y.roll (Y.roof Z W) (horiz x p n)=Y.roll W (horiz x p n):=by
 rw [roll_c,roll_c,heir_h]; unfold spec; cases e:Y.find x p n; exact rfl; rename_i d; exact if_neg (show d.1∉Z from Y.locate i x p n h hv e ▸ u) -- syntax
lemma roll_short {Z:Finset Y.Col}{K:ℝ}(W:Y.Branch)(h:∀ i:Y.Door,i.1∉Z→‖W i‖≤K)(u:0≤K)(b:Bond s): ‖Y.roll (Y.roof Z W) b‖≤K:=by rw [roll_c,spec]; cases e:Y.heir b; simpa [spec] using u; rename_i i; change ‖Y.roof Z W i‖≤_; unfold roof; split; rwa [norm_zero]; exact h i ‹_› -- tune
end YM.CF.BProof.Angular.Yard
