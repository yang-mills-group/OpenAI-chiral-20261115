import SatinThinTooth
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Ione Moto
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Taxi
open Vow
local notation "G₅"=> SU.group
local notation "re" s:max=> PlaqAxes.transform s
lemma cost_sub (s:Sweep n)(f g:Skate) : costSkate s (f-g)=costSkate s f-costSkate s g:=funext₂ fun i j=>by simp only [costSkate,Pi.sub_apply,map_sub,smul_sub]
lemma cost_scale (s:Sweep n)(f:Skate)(k:ℝ): costSkate s (k • f)= k • costSkate s f:=funext₂ fun i j=>by simp only [costSkate,Pi.smul_apply,map_smul]; rw [smul_comm]
lemma cost_zero (s:Sweep n): costSkate s 0=0:=by unfold costSkate; ext i j; simp -- too many complex ext
lemma cost_contract (s:Sweep n)(f:Skate): ‖costSkate s f‖≤‖f‖:=by
 refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>(pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=>?_
 obtain ⟨i,rfl⟩:=(re s.s).surjective i; obtain ⟨j,rfl⟩:=(re s.s).surjective j; rw [cost_price,norm_smul, Real.norm_eq_abs,abs_mul, scar_abs,scar_abs,one_mul,one_mul,castT]; generalize wageZ s⁻¹=k; have p: ‖f i j‖ ≤ ‖f‖ := (norm_le_pi_norm (f i) j).trans (norm_le_pi_norm f i); cases k; exact p; simpa [cSignX]
lemma wageInv (s:Sweep n): wageZ s⁻¹=wageZ s:=by
 have hp : detX (s.s)⁻¹ = detX s.s:=by have hu:=det_p s.s s.s⁻¹; rw [mul_inv_cancel,det_i] at hu; cases h: detX s.s<;>cases g:detX s.s⁻¹<;>simp [h,g] at hu ⊢
 change s.charge.xor _=_; rw [show (s⁻¹).s = s.s⁻¹ from rfl,hp]; rfl

-- Target weights (here not Frobenius normed -- instead sup-norm one)
private theorem ord_cases (x:PlaqAxes): x.val=(0,1)∨x.val=(0,2)∨x.val=(0,3)∨x.val=(1,2)∨x.val=(1,3)∨x.val=(2,3):=by revert x; decide
abbrev lowLow : PlaqAxes:= ⟨(0,1),by decide⟩
abbrev rimA : PlaqAxes:= ⟨(0,2),by decide⟩
abbrev rimB : PlaqAxes:= ⟨(0,3),by decide⟩
abbrev rimC : PlaqAxes:= ⟨(1,2),by decide⟩
abbrev rimD : PlaqAxes:= ⟨(1,3),by decide⟩
abbrev highHigh : PlaqAxes:= ⟨(2,3),by decide⟩
lemma rimCases (x:PlaqAxes): x=lowLow∨x=rimA∨x=rimB∨x=rimC∨x=rimD∨x=highHigh:=by
 simp only [Subtype.ext_iff]; exact ord_cases x
/-- Real weight and line. -/
def starWeight (x:PlaqAxes):ℝ:= if x=rimA∨x=rimD then 1 else if x=rimB∨x=rimC then -1 else 0
def mainSlot : Skate:=fun i j=>if i=j then ↑(starWeight i) else 0
lemma star_thin (s:Signed)(h:Quad s) (i:PlaqAxes) : starWeight ((re s) i)=tax s*starWeight i:=by
 let z:=s.perm; have hp (t:Equiv.Perm Axis)(p:z=t) : (re s) i = PlaqAxes.rotate (Pec.X t) i ∧ tax s=tax (Pec.X t):=by
    refine ⟨?_,congrArg (fun p:Equiv.Perm Axis=> (↑((Equiv.Perm.sign p):ℤ):ℝ)) p⟩
    apply Subtype.ext; change (min (z i.val.1) (z i.val.2),max _ _) = (min _ _,max _ _); unfold z
    rw [show s.perm=t from p]; rfl
 rcases h.lo with ⟨a,b⟩|⟨a,b⟩ <;> rcases h.hi with ⟨c,d⟩|⟨c,d⟩
 · obtain ⟨p,t⟩:= hp 1 (Equiv.ext fun i=> by unfold z; fin_cases i; exact a; exact b; exact c; exact d) -- swapDec rfl?
   rw [p,t]; have hz:tax (Pec.X 1)=1:=by exact tax_o
   rw [hz]; rcases rimCases i with h|h|h|h|h|h<;>subst i
   · change 0= 1 * (0:ℝ); ring
   · change 1= 1 * (1:ℝ); ring
   · change (-1)= 1 * ((-1):ℝ); ring
   · change (-1)= 1 * ((-1):ℝ); ring
   · change 1= 1 * (1:ℝ); ring
   · change 0= 1 * (0:ℝ); ring
 · obtain ⟨p,t⟩:= hp (Equiv.swap 2 3) (Equiv.ext fun i=> by unfold z; fin_cases i; exact a; exact b; exact c; exact d) -- swapDec rfl?
   rw [p,t]; have hz:tax (Pec.X (Equiv.swap 2 3))= -1:=by exact tax_s _ _ (by decide)
   rw [hz]; rcases rimCases i with h|h|h|h|h|h<;>subst i
   · change 0= (-1) * (0:ℝ); ring
   · change (-1)= (-1) * (1:ℝ); ring
   · change 1= (-1) * ((-1):ℝ); ring
   · change 1= (-1) * ((-1):ℝ); ring
   · change (-1)= (-1) * (1:ℝ); ring
   · change 0= (-1) * (0:ℝ); ring
 · obtain ⟨p,t⟩:= hp (Equiv.swap 0 1) (Equiv.ext fun i=> by unfold z; fin_cases i; exact a; exact b; exact c; exact d) -- swapDec rfl?
   rw [p,t]; have hz:tax (Pec.X (Equiv.swap 0 1))= -1:=by exact tax_s _ _ (by decide)
   rw [hz]; rcases rimCases i with h|h|h|h|h|h<;>subst i
   · change 0= (-1) * (0:ℝ); ring
   · change (-1)= (-1) * (1:ℝ); ring
   · change 1= (-1) * ((-1):ℝ); ring
   · change 1= (-1) * ((-1):ℝ); ring
   · change (-1)= (-1) * (1:ℝ); ring
   · change 0= (-1) * (0:ℝ); ring
 · obtain ⟨p,t⟩:= hp (Equiv.swap (0:Axis) 1 * Equiv.swap 2 3) (Equiv.ext fun i=> by unfold z; fin_cases i; exact a; exact b; exact c; exact d) -- swapDec rfl?
   rw [p,t]; have hz:tax (Pec.X (Equiv.swap (0:Axis) 1 * Equiv.swap 2 3))=1:=by rw [show Pec.X (Equiv.swap (0:Axis) 1 * Equiv.swap 2 3)=Pec.X (Equiv.swap 0 1)* Pec.X (Equiv.swap 2 3) from rfl,tax_m,tax_s _ _ (by decide),tax_s _ _ (by decide)]; ring
   rw [hz]; rcases rimCases i with h|h|h|h|h|h<;>subst i
   · change 0= 1 * (0:ℝ); ring
   · change 1= 1 * (1:ℝ); ring
   · change (-1)= 1 * ((-1):ℝ); ring
   · change (-1)= 1 * ((-1):ℝ); ring
   · change 1= 1 * (1:ℝ); ring
   · change 0= 1 * (0:ℝ); ring
lemma scarLine (s:Sweep n)(h:s∈cycleSweep n): costSkate s mainSlot=bandSign s • mainSlot:=by
 funext i j; obtain ⟨i,rfl⟩:=(re s.s).surjective i; obtain ⟨j,rfl⟩:=(re s.s).surjective j; rw [cost_price]; by_cases v:i=j; swap; · simp [mainSlot,v]
 subst j; simp only [mainSlot,Pi.smul_apply,ite_true]; rw [scar_sq,one_smul,castT, star_thin s.s ((cycleQ _).mp h), Complex.ofReal_mul]; change Spire.payZ _ _= _; rw [Tye.pin_z,Complex.real_smul, ←mul_assoc, ←Complex.ofReal_mul, show bandSign s*tax s.s= _ from tax_sq s.s, Complex.ofReal_one,one_mul] -- maybe namespace
lemma slotAt : mainSlot rimA rimA=1:=by norm_num [mainSlot,starWeight]
lemma slotV : Verc mainSlot:=by intro i j; by_cases h:i=j; subst j; rfl; simp [mainSlot,h,Ne.symm h]
lemma slotNorm : ‖mainSlot‖=1:=by
 refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j=>?_) ?_
 · unfold mainSlot starWeight; split_ifs <;> simp
 refine le_trans (le_of_eq ?_) ((norm_le_pi_norm (mainSlot rimA) rimA).trans (norm_le_pi_norm mainSlot rimA)); rw [slotAt,norm_one]

lemma sign_forces (g:Skate)(x:Site n)(t:∀ s:Sweep n,s∈cycleSweep n→ Earlier s x x→ costSkate s g=bandSign s • g): ∃ v:ℝ,g=v • mainSlot:=by
 -- charge true mirror all entries real. simple
 let c:Sweep n:=⟨1,0,true⟩; have hc:c∈cycleSweep n:=quad_id
 let h(s:Sweep n)(w:s∈cycleSweep n)(a:Earlier s x x)(i j:PlaqAxes): (spinScar s.s i*spinScar s.s j) • cSignX (wageZ s) (g i j) = tax s.s • g ((re s.s) i) ((re s.s) j):=by rw [←wageInv s,←castT,←cost_price,t s w a]; rfl
 have ho(i:PlaqAxes): (re (1:Signed)) i=i:=by apply Subtype.ext; change (min (i.val.1) (i.val.2),max (i.val.1) (i.val.2))= i.val; simp [i.property.le]
 have ht(i j:PlaqAxes): star (g i j)=g i j:=by
    have ht:= h c hc (show Earlier c x x from earlier_id x) i j; rw [show c.s=1 from rfl,ho,ho,show wageZ c=true from (by change true.xor (detX 1)=true; rw [det_i]; rfl)] at ht; simpa [spinScar,i.property,j.property,tax_o,sign,cSignX] using ht
 have hp (s:Signed)(q:Quad s)(i j:PlaqAxes):
    (spinScar s i*spinScar s j) • g i j=tax s • g ((re s) i) ((re s) j):=by
    obtain ⟨a,u,p,l⟩:=poseAll s x x; have hh:= h a (cycleQ _|>.mpr (u.symm ▸ q)) l i j; rw [u] at hh; cases wageZ a<;> simpa [cSignX,ht] using hh
 have hu (p q:Axis)(z:ℂ)(h:z= -z): z=0:=by -- dummy unused!
    rcases eq_or_ne z 0 with x|x; exact x; have ht: z+z=0:=eq_neg_iff_add_eq_zero.mp h
    exact False.elim (mul_ne_zero (by norm_num:(2:ℂ)≠0) x (by rw [two_mul]; exact ht))
 have hx(i j:PlaqAxes)(p:i≠j):g i j=0:=by
    have hv (t:Axis):=hp (Signed.mirror t) (quad_mirror t) i j; have hm(t:Axis)(k:PlaqAxes): (re (Signed.mirror t)) k=k:=ho k -- defEq
    have h₁:=i.property; have h₂:=j.property; have he:i.val.1 ≠ j.val.1 ∨ i.val.2 ≠ j.val.2:= by grind -- as Averaging
    rcases (show (i.val.1≠j.val.1 ∧ i.val.1≠j.val.2)∨(i.val.2≠j.val.1∧i.val.2≠j.val.2) by grind) with ⟨x,y⟩|⟨x,y⟩
    · apply hu 0 0; specialize hv i.val.1; rw [hm,hm,tax_mi] at hv; simpa [sign,spinScar,x,y,h₁,h₂, Signed.mirror,h₁.ne] using hv.symm
    apply hu 0 0; specialize hv i.val.2; rw [hm,hm,tax_mi] at hv; simpa [sign,spinScar,x,y,h₁,h₂,Signed.mirror,Ne.symm h₁.ne] using hv.symm
 have hc (i:PlaqAxes)(s:Signed)(q:Quad s) : g i i=tax s • g ((re s) i) ((re s) i):=by have he:=hp s q i i; simpa only [scar_sq,one_smul] using he
 let v:ℝ := (g rimA rimA).re; have hA: (↑v:ℂ) =g rimA rimA:= Complex.conj_eq_iff_re.mp (ht ..) -- tune
 refine ⟨v,funext₂ fun i j=>?_⟩; simp only [Pi.smul_apply,mainSlot]; split_ifs with p; swap; · rw [hx i j p,smul_zero]
 subst j
 let t:= Pec.X (Equiv.swap 0 1); let s:=Pec.X (Equiv.swap 2 3)
 have hB:= hc rimA s quad_swap_hi; have hC:= hc rimA t quad_swap_lo
 rw [show (re s) rimA=rimB from by unfold s; decide,show tax s= -1 from tax_s _ _ (by decide),neg_one_smul] at hB; rw [show (re t) rimA=rimC from by unfold t; decide,show tax t= -1 from tax_s _ _ (by decide),neg_one_smul] at hC
 have hD:= hc rimB t quad_swap_lo; rw [show (re t) rimB=rimD from by unfold t; decide,show tax t= -1 from tax_s _ _ (by decide),neg_one_smul] at hD
 rcases rimCases i with a|a|a|a|a|a<;>subst i
 · rw [show starWeight lowLow=0 from rfl,Complex.real_smul]; simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,Complex.ofReal_neg,mul_neg,mul_one,hA]
   have p:= hc lowLow s quad_swap_hi; rw [show (re s) lowLow=lowLow from by unfold s; decide,show tax s= -1 from tax_s _ _ (by decide),neg_one_smul] at p; exact hu 0 0 _ p
 · rw [show starWeight rimA=1 from rfl,Complex.real_smul]; simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,Complex.ofReal_neg,mul_neg,mul_one,hA]
 · rw [show starWeight rimB=(-1) from rfl,Complex.real_smul]; simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,Complex.ofReal_neg,mul_neg,mul_one,hA]
   rw [hB,neg_neg]
 · rw [show starWeight rimC=(-1) from rfl,Complex.real_smul]; simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,Complex.ofReal_neg,mul_neg,mul_one,hA]
   rw [hC,neg_neg]
 · rw [show starWeight rimD=1 from rfl,Complex.real_smul]; simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,Complex.ofReal_neg,mul_neg,mul_one,hA]
   rw [hB,hD,neg_neg]
 · rw [show starWeight highHigh=0 from rfl,Complex.real_smul]; simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,Complex.ofReal_neg,mul_neg,mul_one,hA]
   have p:= hc highHigh s quad_swap_hi; rw [show (re s) highHigh=highHigh from by unfold s; decide,show tax s= -1 from tax_s _ _ (by decide),neg_one_smul] at p; exact hu 0 0 _ p
end YM.CF.QuadClock
