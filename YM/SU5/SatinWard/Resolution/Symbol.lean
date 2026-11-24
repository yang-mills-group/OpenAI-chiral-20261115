import YM.SU5.SatinWard.Resolution.Chamber

/-!
# The X/W characters and spin probe action
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU

/-- We only actually need the generated two-plane motions. -/
def pseudoCharacter(n:Side) : SweepSign n where
 group := twoPlanes n
 fits := le_rfl
 translations _:=Loomed.one_mem
 sgn s := hush s.charge 1
 mult {s t} _ _ := by change hush (s.charge.xor t.charge) _ = _; cases s.charge <;> cases t.charge <;> norm_num
 sq {s} _ := by cases s.charge <;> norm_num
 space _:= rfl

lemma grows_pseudo {n m:Side}(G:Ratio n m):Grows G (pseudoCharacter n) (pseudoCharacter m):=
 ⟨fun _ h=>reSweep_twoPlanes G h, fun _ _=>rfl⟩

def flipGroup(n:Side): Subgroup (Sweep n) where
 carrier:={x| x∈twoPlanes n ∧ x.s.perm=1 ∧ x.charge=false}
 one_mem':=⟨(twoPlanes n).one_mem,rfl,rfl⟩
 inv_mem':=fun {i} ⟨a,hBr,c⟩=> ⟨(twoPlanes n).inv_mem a,show i.s.perm⁻¹= (1:Equiv.Perm Axis) by rw [hBr,inv_one],c⟩
 mul_mem':=fun {i j} ⟨t,h,a⟩ ⟨s,w,hBr⟩=>⟨(twoPlanes n).mul_mem t s,show i.s.perm*j.s.perm= (1:Equiv.Perm Axis) by rw [h,w,mul_one], show i.charge.xor j.charge=false by rw [a,hBr]; rfl⟩

def spinCharacter (n:Side)(i:Axis) : SweepSign n where
 group := flipGroup n
 fits := fun _ a=> a.1
 translations _:=⟨Loomed.one_mem,rfl,rfl⟩
 sgn s:= sign s.s i
 mult {s t} _ u:=by unfold sign; rw [show (s*t).s=s.s*t.s from rfl,Signed.mul_flip,show t.s.perm=1 from u.2.1]; cases h:t.s.flip i <;> cases p:s.s.flip i<;> simp [p]
 sq {s} _:=by unfold sign; split_ifs<;>norm_num
 space _:= rfl

lemma grows_spin {n m:Side}(G:Ratio n m)(i:Axis):Grows G (spinCharacter n i) (spinCharacter m i):=by
 constructor
 · intro s p; change s∈flipGroup n at p
   change _ ∧ (_:Prop) ∧ (_:Prop); exact ⟨reSweep_twoPlanes G p.1,p.2⟩
 intro s h; rfl

abbrev allFourFlip:=Signed.mirror 0 * Signed.mirror 1 * Signed.mirror 2 * Signed.mirror 3
lemma allFourApply : ∀ i:Axis, sign allFourFlip i= -1 := by
 have h:∀ i:Axis, allFourFlip.flip i=true := by decide
 simp [sign,h]
lemma det_allFour:detX allFourFlip=false:=by simp [allFourFlip,det_p,det_t]
lemma allFour_mem:allFourFlip∈ Loomed:=mul_mem (mul_mem (mul_mem (mirror_l _) (mirror_l _)) (mirror_l _)) (mirror_l _)
lemma mem_spin (v:Axis)(s:Sweep n): s∈(spinCharacter n v).group ↔ s.s∈ Loomed∧s.s.perm=1∧s.charge=false:=Iff.rfl

lemma neg_forces{X:Type*}[AddCommGroup X][IsAddTorsionFree X](a:X)(p:a= -a): a=0:=by
 have h:a+a=0:=eq_neg_iff_add_eq_zero.mp p; exact (smul_right_injective X (show (2:ℕ)≠0 from by norm_num)) (by change (2:ℕ)• a = _ • (0:X); rwa [smul_zero,two_smul])

lemma spin_no_offset (n:Side)(i:Axis):(spinCharacter n i).KillsScalar:=by
 intro F t; funext x; obtain ⟨s,w,a,h⟩:=poseAll allFourFlip x x; have ht: s ∈ (spinCharacter n i).group:=(mem_spin ..).2 ⟨w.symm ▸ allFour_mem, (show s.s.perm=1 by rw [w]; rfl),a⟩
 have hp:= t s ht x x h; rw [tρ,ContinuousLinearMap.coe_coe,phaseB,wageInv,castT,show wageZ s=false from by unfold wageZ; rw [a,w,det_allFour]; rfl,show (spinCharacter n i).sgn s= -1 from (show sign s.s i = -1 by rw [w,allFourApply]),neg_one_smul] at hp
 exact neg_forces _ hp

lemma pseudo_no_offset (n:Side):(pseudoCharacter n).KillsScalar:=by
 intro F t; funext x; let c:Sweep n:=⟨1,0,true⟩; obtain ⟨s,w,a,h⟩:=poseAll (Signed.mirror 3) x x
 let χ:=pseudoCharacter n
 have he(i:Sweep n)(v:i∈χ.group)(p:Earlier i x x)(w:wageZ i=true): star (F x)=hush i.charge (1:ℝ) • F x:=by have h:=t i v x x p; rw [tρ,ContinuousLinearMap.coe_coe,phaseB,wageInv,castT,w] at h; exact h
 have hx:c∈χ.group:= Loomed.one_mem
 apply neg_forces; have ht:= he s (show s.s ∈ Loomed from (by rw [w]; exact mirror_l _)) h (by unfold wageZ; rw [a,w,det_t]; rfl); rw [a,hush_false, one_smul] at ht
 rw [← ht] -- probably rewrites both: adjust
 -- goal star Fx=-star Fx; use ht again
 have ph:= he c hx (show Earlier c x x from earlier_id x) (by change true.xor (detX 1)= _; rw [det_i]; rfl)
 simp only [show c.charge=true from rfl,hush_true,neg_one_smul] at ph
 exact (congrArg Neg.neg ht).symm ▸ ph

-- Need exact PH representation *including* charge-odd torus motions.
open Fir
private lemma pet_right (i:Axis): Aop*gammaOp i=gammaOp i*(1-Aop):=by
 simp only [Adef,Matrix.mul_smul,Matrix.smul_mul,mul_sub, add_mul, mul_add,mul_one,one_mul, gradingSwap]; module
lemma pet_star(i:Axis):star (petal i)=(-(Complex.I/2):ℂ) • ((1-Aop)*gammaOp i):=by
 rw [petal,star_smul,star_mul,(gammaAdj _).star_eq,Aadj, sub_mul,one_mul,pet_right,mul_sub,mul_one]; norm_num; module

variable {s:Signed}{U:UNI SpinIdx}{a b:Bool}
lemma pet_forward (b:Bool)(E:JetS s b false U)(i:Axis): sings b U (petal (s.perm i))= hush b (hush (s.flip i) (petal i)):=by
 conv_lhs=> rw [petal,singT,win_c,twist_scalar,win_m,map_mul,←singT,←singT,E.cliff, show sings b U Aop=Aop from angleX E true]
 cases b; exact (by cases h:s.flip i<;>simp [petal,cSignX]); cases h:s.flip i <;> simp [neg_div,cSignX,petal]
lemma pet_reverse (b:Bool)(E:JetS s b true U)(i:Axis): sings b U (petal (s.perm i))= hush b (-star (hush (s.flip i) (petal i))):=by
 conv_lhs=> rw [petal,singT,win_c,twist_scalar,win_m,map_mul,←singT,←singT,E.cliff, show sings b U Aop=1-Aop from angleX E true]
 cases b<;> cases h:s.flip i <;> simp only [star_neg,hush_true,hush_false,pet_star,neg_smul,neg_neg,mul_neg,smul_neg] <;> simp [cSignX,neg_div]

lemma castPet (p:JetS s a b U)(i:Axis)(x:Op SU.Slot): castPal a b U (petal (s.perm i) ⊗ₖ x)
    = hush a (hush (s.flip i) (petal i ⊗ₖ (if b then star (windX a x) else windX a x))):= by
 unfold castPal; rw [show sings a (twoU U a) _= _ from wingK U (xtra a) (petal _) x, singT (p:=a) (xtra a).V,show (xtra a).V=1 from rfl,one_des]; cases b
 · rw [pet_forward a p]; cases h:s.flip i <;> cases a <;> simp [op_kron_neg,Thera.jazz]
 rw [pet_reverse a p]; cases h:s.flip i <;> cases a <;> simp only [hush_true,hush_false,Thera.jazz,ite_true,star_neg,op_star_kron,star_star,neg_neg,op_kron_neg]
section
local notation "EndC"=> Op SU.Slot
open Ember
lemma minus_unique{A:Type*}[AddCommGroup A][Module ℝ A](x:A)(p:x= -x):x=0:=by
 have h:(2:ℝ) • x=0:=by rw [two_smul]; exact eq_neg_iff_add_eq_zero.mp p
 exact (smul_eq_zero.mp h).resolve_left (by norm_num)
lemma pet_normShape (i:Axis)(A:EndC):Binned (petal i ⊗ₖ A):= by
 unfold Binned
 rw [show 1-bins SU.Slot=(1-Aop)⊗ₖ (1:EndC) from by simp only [bins,sub_eq_add_neg _ _, Matrix.add_kronecker,Matrix.one_kronecker_one,op_kron_neg]]
 rw [bins, op_kron_mul,op_kron_mul, one_mul,mul_one,petal, Matrix.mul_smul,Matrix.smul_mul,←mul_assoc Aop,AOne, pet_right]
 congr 2; rw [mul_assoc, show (1-Aop)*(1-Aop)=1-Aop from by rw [sub_mul,one_mul,mul_sub,mul_one,AOne]; abel]
lemma commutes_petal (v:Axis)(A:EndC)(g:SU.E): Commute (petal v⊗ₖ A) (KinX g) ↔ Commute A (matter g).val:=by
 unfold KinX Commute SemiconjBy; rw [op_kron_mul,op_kron_mul,mul_one,one_mul]; exact (spa_i v).eq_iff
lemma pet_hush (v:Axis)(A:EndC)(b:Bool): petal v⊗ₖ hush b A=hush b (petal v⊗ₖ A):=by cases b; rfl; rw [hush_true,hush_true,←neg_one_smul ℂ A,op_kron_smul,neg_one_smul]
lemma sign_hush (s:Signed)(i:Axis)(X:Pal): sign s i • X=hush (s.flip i) X:=by unfold sign; cases s.flip i<;>norm_num

lemma twist_expand {c:Signed}{U:UNI SpinIdx}(p:JetS c false false U)(X:Pal)(h:Binned X):
    castPal false false U X = ∑ i:Axis, petal i⊗ₖ hush (c.flip i) (spaX X (c.perm i)):=by
 change twist _ X=_; conv_lhs=> rw [←h,←spa_p,map_sum,←Equiv.sum_comp c.perm]
 exact sum_congr rfl fun i _=> (castPet p i _).trans (pet_hush i (spaX X (c.perm i)) (c.flip i)).symm
lemma flip_slice {c:Signed}{U:UNI SpinIdx}(p:JetS c false false U)(X Y:Pal)(h:Binned X)(_k:Binned Y)(e:castPal false false U X=Y)(i:Axis): hush (c.flip i) (spaX X (c.perm i))=spaX Y i:=by
 rw [twist_expand p _ h] at e; exact (spa_s i _).symm.trans (congrArg (fun A=>spaX A i) e)
lemma invariant_slice (i:Axis)(X:Pal)(h:Binned X)
    (p:∀ c:Signed,c∈ Loomed→c.perm=1→ c.flip i=false→ ∀ (_q:detX c=false),castPal false false (spinU false c) X=X):
    X=petal i ⊗ₖ spaX X i:=by
 have hr(j:Axis)(a:j≠i): spaX X j=0:=by
    obtain ⟨k,v,t⟩:=(show ∀ i j:Axis,∃ k:Axis,i≠k∧j≠k from by decide) i j
    let c:= Signed.mirror j*Signed.mirror k; have hu:detX c=false:=by unfold c; rw [det_p,det_t,det_t]; rfl
    have ht:= flip_slice (c:=c) (U:=spinU false c)
                    (by simpa only [hu] using (spinZ false c)) X X h h
                    (p c (mul_mem (mirror_l _) (mirror_l _)) rfl (by simp [c,a,v.symm,Signed.mirror]) hu) j
    rw [show c.flip j=true from by simp [c,t.symm,Signed.mirror]] at ht; exact minus_unique _ ht.symm
 conv_lhs=> rw [←h,←spa_p];
 rw [sum_eq_single i]; intro j _ v; rw [hr j v]; simp; simp
lemma flip_negates {u:UNI SpinIdx}(p:JetS allFourFlip false false u)(X:Pal)(h:Binned X): castPal false false u X = -X:=by
 rw [twist_expand p _ h]; simp_rw [(show ∀ i:Axis, allFourFlip.flip i=true from by decide),pet_hush,hush_true,(show ∀ i:Axis, allFourFlip.perm i=i from by decide), sum_neg_distrib]; rw [spa_p,h] -- tune h unwrap

lemma spin_bin (A:Pal)(h:A∈mind_B): Binned A:=h.1
lemma jetsBin (X:partZ)(h:X∈mind_C)(i:Axis): X.1 i∈ mind_B∧ X.2 i∈mind_B:=⟨h.1 i,h.2 i⟩
lemma spin_sgn_inv (i:Axis)(b:Sweep n)(h:b.s.perm=1): (spinCharacter n i).sgn b⁻¹= (spinCharacter n i).sgn b:=by change sign b.s⁻¹ i=_; simp [sign,h,spinCharacter]; rfl

structure ChiralX (v:Axis)(X:EndC):Prop where -- v unused
 color(g:SU.E):Commute X (matter g).val
 herm:star X=X

abbrev spinShape(v:Axis)(X:Op SU.Slot):ArcΦ:=(0,petal v⊗ₖ X,0)

lemma current_sector (n:Side)(v:Axis)(X:ArcΦ):
    (InΦ X ∧ (spinCharacter n v).Eigenspace X) ↔ ∃ F:EndC, X=spinShape v F ∧ ChiralX v F:= by
 let χ:=spinCharacter n v
 constructor
 · rintro ⟨h,q⟩; obtain ⟨p,h,x⟩:=h
   have he(c:Signed)(hc:c∈ Loomed)(g:c.perm=1): coinArc c false (detX c) (spinU false c) X.2= sign c v • X.2:=by
      let b':Sweep n:=⟨c,0,false⟩
      have hp:=congrArg Prod.snd (q b'⁻¹ (χ.group.inv_mem ((mem_spin v _).2 ⟨hc,g,rfl⟩)))
      change costDome b'⁻¹ X.2= (spinCharacter n v).sgn b'⁻¹ • X.2 at hp; rw [costDome,inv_inv, spin_sgn_inv v b' g] at hp; exact hp
   let Y:= spaX X.2.1 v; have hb:= spin_bin X.2.1 h
   have hz:X.2.1=petal v⊗ₖ Y := invariant_slice v X.2.1 hb (fun c e t l w=> by
      have h:= congrArg Prod.fst (he c e t); rw [w, sign,l] at h; simp only [Bool.false_eq_true, ↓reduceIte,one_smul] at h; exact h)
   have hsp:ChiralX v Y:=by
      constructor
      · intro g; apply (commutes_petal ..).1; rw [←hz]; exact h.2 g
      have ht:=congrArg Prod.fst (he (Signed.mirror v) (mirror_l v) rfl); let U:=spinU false (Signed.mirror v)
      rw [det_t] at ht; change castPal false true U X.2.1=sign _ v • X.2.1 at ht; rw [sign_hush,hz] at ht; have he:=castPet (s:=Signed.mirror v) (U:=U) (a:=false) (b:=true) (by simpa only [det_t] using (spinZ false (Signed.mirror v))) v Y; rw [show (Signed.mirror v).perm v = v from rfl] at he; rw [he] at ht
      simp only [hush_false] at ht; rw [show (Signed.mirror v).flip v=true from by simp [Signed.mirror], hush_true,hush_true] at ht; exact spa_i _ (neg_injective ht)
   refine ⟨Y,Prod.ext ?_ (Prod.ext hz ?_),hsp⟩
   · let s:Sweep n:=⟨allFourFlip,0,false⟩; have t0:=congrArg Prod.fst (q s ((mem_spin v _).2 ⟨allFour_mem,rfl,rfl⟩)); change costSkate s X.1=sign allFourFlip v • X.1 at t0; rw [allFourApply,neg_one_smul, show costSkate s X.1= X.1 from ?_] at t0; exact minus_unique _ t0
     funext i j; have hz(t:PlaqAxes):PlaqAxes.transform s.s t=t:=Subtype.ext (Prod.ext (min_eq_left t.property.le) (max_eq_right t.property.le)); have hp:=cost_price s X.1 i j; have hv(t:PlaqAxes):spinScar s.s t=1:=by unfold spinScar; change sign allFourFlip _ * sign allFourFlip _ *_=1; rw [if_pos (show s.s.perm t.val.1<s.s.perm t.val.2 from t.property),allFourApply,allFourApply]; norm_num
     rw [hz,hz,hv,hv,one_mul,one_smul,castT,wageInv,show wageZ s=false from (by change false.xor (detX allFourFlip)=_; rw [det_allFour]; rfl)] at hp; exact hp
   have ht:=he allFourFlip allFour_mem rfl; rw [allFourApply, neg_one_smul,det_allFour] at ht; let U:=spinU false allFourFlip
   have H:JetS allFourFlip false false U:=by simpa only [U,det_allFour] using (spinZ false allFourFlip)
   apply Prod.ext
   · funext i; have hp:= congrFun (congrArg (fun v:Dome=> v.2.1) ht) i; change sign allFourFlip i • castPal false false U (X.2.2.1 i)= -(X.2.2.1 i) at hp; rw [flip_negates H _ (spin_bin _ (jetsBin _ x i).1),allFourApply,neg_one_smul,neg_neg] at hp; exact minus_unique _ hp
   funext i; have hp:= congrFun (congrArg (fun v:Dome=> v.2.2) ht) i; change sign allFourFlip i • castPal false false U (X.2.2.2 i)= -(X.2.2.2 i) at hp; rw [flip_negates H _ (spin_bin _ (jetsBin _ x i).2),allFourApply,neg_one_smul,neg_neg] at hp; exact minus_unique _ hp
 rintro ⟨F,rfl,w,x⟩
 refine ⟨⟨mind_A.zero_mem,?_,mind_C.zero_mem⟩,fun s a=>?_⟩
 · exact And.intro (show culm _=petal v ⊗ₖ F from pet_normShape v F) (fun g=> (commutes_petal ..).2 (w g))
 obtain ⟨s,b,t⟩:=s; obtain ⟨i,g,rfl⟩:=(mem_spin ..).1 a -- last rfl
 change (costSkate ⟨s,b,false⟩ 0, coinArc s⁻¹ false _ _ (petal v⊗ₖ F,0)) = sign s v • spinShape v F
 refine Prod.ext ?_ (Prod.ext ?_ ?_)
 · rw [cost_zero]; exact (smul_zero _).symm
 · have ht: s⁻¹.perm v=v:=by change s.perm.symm v=_; rw [show s.perm=1 from g]; rfl
   have he:= castPet (spinZ false s⁻¹) v F; rw [ht] at he; let t':Sweep n:=⟨s,b,false⟩; change castPal false (detX s⁻¹) (spinU false s⁻¹) (petal v⊗ₖ F)=sign s v • (petal v⊗ₖ F); rw [he, ← show sign s⁻¹ v= sign s v from spin_sgn_inv v t' g,sign_hush,hush_false]; split; exact congrArg (fun X=> hush (s⁻¹.flip v) (petal v⊗ₖ X)) x; rfl
 change jetTurn (Sweep.mk s b false) 0= _; suffices jetTurn (Sweep.mk s b false) 0=0 by rw [this]; exact (smul_zero _).symm
 exact congrArg Prod.snd (dome_zero _)
end
end YM.CF.QuadClock
