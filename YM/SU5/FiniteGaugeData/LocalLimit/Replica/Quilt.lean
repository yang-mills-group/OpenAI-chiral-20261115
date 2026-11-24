import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Squeeze
import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Street

/-! # Replica copies : charge local before requiring any period subsequence or uniform estimates

The copy bound spends squares and transport on the Donor heat ratio, over its given
price. The floorplan parameters count any requested number of DOUBLINGS in each
axis, smaller than or equal to what's needed to reach the edges, with the same
buffer margin from both ends on each reflection. No wrapping across those margins.
Single axes may be used independently. (`quilt` theorem uses equal number of
doublings for all four.) -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window.SquareScalar
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Lat Cube RP Push.GridApprox Cells
open scoped Classical Topology BigOperators ContDiff InnerProductSpace ComplexOrder ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
variable {P:Patch}{m B:Side}
variable (d:ℕ)(c:RoomCount)(s: Axis)
local notation "Nt" => CSide m B
local notation "N'" => More (CSide m B)
local notation "Γ" => Config SU.group (More (CSide m B))
-- invariant expectation on support in Q (proof only at that permit)
structure FrameBill (P:Patch)(m B:Side)(F:Evaluation (CSide m B)→ℂ) : Prop where
 mass : F 1=1
 travel (x:Cover)(X:Config SU.group (More (CSide m B))→ℂ): Envelope X → F (bosonic (CSide m B) (X ∘ Lattice.pull 1 (wrap _ ((2*B.val) • x))))= F (bosonic (CSide m B) X)
 cost (s:Axis) (X:Fin 2 → Config SU.group (More (CSide m B))→ℂ)(h:∀ i,ξTape s P _ (X i)): (reflectionForm s F (fun i=>bosonic (CSide m B) (X i))).PosSemidef
abbrev widths (s:Axis)(c:RoomCount)(l:ℕ) := update c s (c s+l)
def ribbon (d:ℕ)(c:RoomCount)(s: Axis) {N:Side} (X:Config SU.group (More N)→ℂ): ℕ → Config SU.group (More N)→ℂ
 | 0=> X
 | n+1=> copy s d (widths s c n) (ribbon d c s X n)
lemma widths_zero: widths s c 0=c:=by unfold widths; simp
lemma widths_add (l:ℕ): widths s c (l+1)=spanAlong s (widths s c l):=by
 unfold spanAlong widths; rw [update_self,update_idem, Nat.add_assoc]
variable (F:Evaluation (CSide m B)→ℂ)(H:FrameBill P m B F)(A : Config SU.group (More (CSide m B))→ℂ){w:ℝ}(hw:boxed P d c w A)(hd:2*B.val∣d)
include H hw hd
open FrameBill
local notation "Rh" X => F (bosonic (CSide m B) X)
lemma copies_once (e: d*2^c s ≤ (CSide m B).val) : ‖Rh A‖^2 ≤ ‖Rh (copy s d c A)‖ := by
 have hz:= hw.localB; have ht:Envelope A:= ⟨hz.borel,hz.cost⟩; apply (unit_price F A s H.mass (hz.enlarges (rayRoom d s c e)) (H.cost s)).trans_eq; obtain ⟨v,e⟩:= hd
 have he: ferry s d c=(2*B.val) • ((v*2^(c s)) • step s) := by unfold ferry; rw [e,mul_assoc,smul_smul]
 unfold copy; rw [he,H.travel _ (θBack s A * A) ((θ_back_env s ht).mulC ht)]
lemma prismBill (l:ℕ)(e: d*2^(c s+l) ≤ (CSide m B).val):
    boxed P d (widths s c l) (w^(2^l:ℕ)) (ribbon d c s A l) ∧
    ‖Rh A‖^(2^l:ℕ) ≤ ‖Rh (ribbon d c s A l)‖ := by
 induction l with
 | zero=> rw [widths_zero]; exact ⟨by simpa [ribbon] using hw, by simp [ribbon]⟩
 | succ i ih=>
    have hv: d*2^(c s+i) ≤ (CSide m B).val:= le_trans ?_ e; swap; · gcongr <;> omega
    obtain ⟨a,b⟩ := ih hv
    rw [pow_succ (2:ℕ),pow_mul,pow_mul,widths_add]; let V:=ribbon d c s A i; let y:=widths s c i
    exact ⟨copy_cost _ _ _ V a, (pow_le_pow_left₀ (by positivity) b _).trans (copies_once d y s F H V a hd (by rw [show y s=c s+i from update_self ..]; exact hv))⟩

-- fix order and lay out this grid of gauge-grid marks
def bedroom(n:ℕ)(s:ℕ):RoomCount:= fun i=>if i.val < s then n else 0
def quilt(d:ℕ)(A:Config SU.group (More (CSide m B))→ℂ)(l:ℕ): Γ→ℂ :=
 let f:=ribbon d (bedroom l 0) 0 A l
 let g:=ribbon d (bedroom l 1) 1 f l
 let h:=ribbon d (bedroom l 2) 2 g l
 ribbon d (bedroom l 3) 3 h l
omit hw
lemma per_tile (l:ℕ)(v:boxed P d (bedroom l 0) w A)(e:d*2^l≤ (CSide m B).val) :
    boxed P d (bedroom l 4) (w^((2^l:ℕ)^4)) (quilt d A l) ∧
    ‖Rh A‖^((2^l:ℕ)^4) ≤ ‖Rh (quilt d A l)‖ := by
 have ht (s:Axis) : widths s (bedroom l s.val) l=bedroom l (s.val+1):=by
    ext i; by_cases h:i=s
    · subst i; simp [bedroom]
    simp only [update_of_ne h,widths]; unfold bedroom; have hv:i.val≠s.val:=fun v=> h (Fin.ext v); split_ifs <;> omega
 let P1:=(2^l:ℕ); let ca(i:ℕ):= bedroom l i
 have he(i:Axis) (A:Γ→ℂ) (w:ℝ)(p:boxed P d (ca i.val) w A): boxed P d (ca (i.val+1)) (w^P1) (ribbon d (ca i.val) i A l) ∧ ‖Rh A‖^P1 ≤ ‖Rh (ribbon d (ca i.val) i A l)‖:=
    (show widths i (ca i.val) l=ca (i.val+1) from ht i) ▸ prismBill d (ca i.val) i F H A p hd l (by rw [show ca i.val i=0 from if_neg (lt_irrefl _),zero_add]; exact e)
 let f8:= ribbon d (ca 0) 0 A l; let g8:= ribbon d (ca 1) 1 f8 l; let t8:= ribbon d (ca 2) 2 g8 l
 obtain ⟨a,b⟩:=he 0 A w v; obtain ⟨u,z⟩:=he 1 f8 _ a; obtain ⟨p,q⟩:=he 2 g8 _ u; obtain ⟨v,x⟩:=he 3 t8 _ p
 have hy(t:ℝ): t^ ((2^l:ℕ)^4)=(((t^P1)^P1)^P1)^P1 := by simp only [←pow_mul]; congr 1; unfold P1; ring
 rw [hy w,hy]; exact ⟨v,(le_trans (pow_le_pow_left₀ (by positivity) (le_trans (pow_le_pow_left₀ (by positivity) (le_trans (pow_le_pow_left₀ (by positivity) b _) z) _) q) _) x)⟩
end YM.CF.Window.SquareScalar
