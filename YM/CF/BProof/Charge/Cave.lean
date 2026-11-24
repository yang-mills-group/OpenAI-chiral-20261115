import YM.CF.BProof.Charge.Pan

/- Index system of regularity A(S). Masking the W for severe arguments leaves all regular
properties unchanged, and the L cancellation holds after that one masking choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Charge
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Form Angular Angular.Yard AnalyticBridge.SectorAffine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {s:Side} (Y:Yard s)(M:ℕ)(l:Tile s)(Z:Finset Y.Col)

def rising := ∃ b:Y.Door,l=Sum.inl (Y.rise b)
def Needs (i:Y.Col):= if rising Y l then i=Lens Y l (M:=M) else close Y (Lens Y l (M:=M)) i (3*M)
lemma own_need : Needs Y M l (Lens Y l (M:=M)):=by unfold Needs; split; rfl; exact ⟨rfl,by rw [Grid.dist_self]; omega⟩
-- holds exactly post axial-coordinate selection for each S, before testing labels
def Cave := ∀ i,Needs Y M l i → i∉ Z
lemma Cave.check : Cave Y M l Z ↔ ¬ ∃ i∈Z, Needs Y M l i:=by unfold Cave; simp only [not_exists]; exact forall_congr' fun i=>by tauto
variable (p:Room Y M)
include p
lemma rises_c (b:Y.Door) : Cave Y M (.inl (Y.rise b)) Z↔ b.1∉Z := by
 unfold Cave Needs; split; · rw [recognize Y _ p (ripe Y _ (M:=M)) b rfl]; simp; -- semis wrong
 next h=> exact False.elim (h ⟨b,rfl⟩)
variable {κ y:ℝ}{U:Config SU.group s}(W:Y.Branch){S: Hall s}{F:Y.FaceS}(e:Y.Climate y S U F)(s₀:Y.Evap κ y U W) (h: Stove Y M l)
include h
lemma spread_wet (b: Bond s)(t:Form.Wet (touch M l) b) : Y.Vic (Lens Y l (M:=M)).1 (5*M+2) (time b.1) ∧ Grid.dist (space b.1) (Lens Y l (M:=M)).2 ≤3*M:= by
 refine ⟨warm_touch Y l h b.1 t.1,?_⟩; rw [Grid.dist_symm]; apply Grid.dist_le.mpr; intro i; apply le_trans (b:=separation (pilot l) b.1) (component_le (pilot l-b.1) i.succ); have g:=p.seed; exact (bounded M l t.1).trans (by omega)
include e s₀
lemma cavern (g:Cave Y M l (Y.severe κ y U)): Tall y (Y.roll W) M U l:=by
 by_cases hx:rising Y l
 · obtain ⟨b,rfl⟩:=hx; exact rise_tone Y b s₀ e ((rises_c Y M _ p b).mp g) -- tune
 have hv: Spread (Y.roll W) U y (touch M l):= by
   intro b hp; obtain ⟨hh,he⟩:=spread_wet Y M l p h b hp; let i:=(Lens Y l (M:=M)).1; have hu:4*(5*M+2)+4≤ Y.long:=by have :=p.range; omega
   rcases whichBond b with ⟨x,p,rfl⟩|⟨x,p,j,rfl⟩; exact Y.tone_vert W e s₀ i x p hu hh
   apply Y.tone_horiz W e s₀ i x p j hu hh; apply g; unfold Needs; rw [if_neg hx]; apply And.intro rfl; rw [Grid.dist_symm]; exact le_trans (Eq.le (by rw [horiz,space_join] : Grid.dist p (Lens Y l (M:=M)).2 = Grid.dist (space (horiz x p j).1) (Lens Y l (M:=M)).2)) he
 cases l; swap; · exact hv
 rename_i a
 intro i; refine hv _ ?_
 rw [show sendEdge 1 0 (positions a i)=positions a i from by unfold sendEdge; simp [Step.used,posDir,affine]]; exact curl_positions a i

omit p e h in
lemma evaporate : Y.Evap κ y U (Y.roof (Y.severe κ y U) W) := by
 refine ⟨s₀.enough,s₀.margin,fun i v=>?_,fun i v=>?_⟩
 · rw [roof,if_neg v]; exact s₀.pay _ v
 rw [roof,if_neg v]; exact s₀.small i v
omit e s₀
lemma cave_dep (T:PathData SU.group)(V:Y.Branch)(g:∀ d:Y.Door, Needs Y M l d.1 → W d=V d): linear T M l (Y.roll W)=linear T M l (Y.roll V):=by
 by_cases H:rising Y l
 · obtain ⟨b,rfl⟩:=H; change curlP 1 (Y.rise b) (Y.roll W)= curlP 1 _ _; have ht(d:Y.Door)(hx:d.1=b.1): W d=V d:=g d (by unfold Needs; rw [if_pos (show rising Y (Sum.inl (Y.rise b)) from ⟨b,rfl⟩)]; exact hx.trans (recognize Y _ p h b rfl).symm) -- H gone
   rw [echo,echo,ht b rfl,attends Y b W V (fun i h=>(ht i h).symm)]
 apply touch_grade l _ _ T; intro b a k; rw [roll_c,roll_c]; cases e:Y.heir b; · exact rfl
 rename_i d; exact g d (by rw [Needs,if_neg H]; exact near_touch Y l p h b ⟨a,k⟩ d e)
end YM.CF.BProof.Charge
