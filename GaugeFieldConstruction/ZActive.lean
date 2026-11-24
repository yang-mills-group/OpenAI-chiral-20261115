import GaugeFieldConstruction.Halo
/-!
# y_B for partially active comparison
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Calibration.RawBank Floor Cauchy Row Phys Conj Function Set Filter Wide Cell
open Matter (FlavorIndex)
open scoped BigOperators Topology

structure District where
  g : Bool
  f : Bool → Bool
variable (D : District)
def enlarged (d : Floor) (B : Rotors) := SY (activates D.g) (fun i=>activates (D.f i)) d B
variable {d : Floor}
abbrev EG (B : Rotors) (a : UG d) := (enlarged D _ B (0,a,0,0)).2.1
abbrev EF (B : Rotors) (b : Bool) : Module.End ℂ (UF d) := activates (D.f b) • YF _ B
abbrev EX (B : Rotors) (b : Bool) : Module.End ℂ (UX d) := YX d D.g (D.f b) B
@[simp] lemma rule0 (B : Rotors) (p : UV d) : (enlarged D d B p).1=0:=rfl
lemma ruleG (B : Rotors) (p : UV d): (enlarged D d B p).2.1=activates D.g • YG d B p.2.1:=rfl
lemma ruleF (B : Rotors) (p : UV d) (i:FlavorIndex): (enlarged D d B p).2.2.1 i=EF D B i.1 (p.2.2.1 i):=rfl
lemma ruleX (B : Rotors) (p : UV d) (i:FlavorIndex): (enlarged D d B p).2.2.2 i=EX D B i.1 (p.2.2.2 i):=by
  change activates _ • _ + activates _ • _= YX d _ _ B _
  -- project unroll
  change activates D.g • YX d true false B _ + activates (D.f _) • YX d false true B _= YX d D.g (D.f i.1) B _
  let a :=p.2.2.2 i
  change activates D.g • YX d true false B a + activates (D.f i.1) • YX d false true B a= _
  cases D.g <;> cases D.f i.1 <;> simp only [activates,Bool.false_eq_true, ↓reduceIte,noneX,one_smul,zero_smul,zero_add,add_zero,pinX] <;> rfl
section Law
lemma gunsum (u v : Rotors) (x : UV d): enlarged D d (u+v) x= enlarged D d u x+enlarged D d v x := by
  apply Prod.ext
  · simp
  simp only [Prod.snd_add]; apply Prod.ext
  · simp only [Prod.fst_add,ruleG, YG, Mint.plus (DeckG d) (gCard d) (leavesG d),LinearMap.add_apply,smul_add]
  simp only [Prod.snd_add]; apply Prod.ext
  · ext1 i; rw [ruleF,Prod.fst_add,Pi.add_apply,ruleF,ruleF]; unfold EF YF; rw [Mint.plus (DeckF d) (fCard d) (leavesF d)]; simp
  ext1 i; rw [ruleX,Prod.snd_add,Pi.add_apply,ruleX,ruleX]; unfold EX YX; rw [Mint.plus _ _ (leavesX d D.g (D.f i.1)),LinearMap.add_apply] -- tune
lemma gs (u : Rotors) (c : ℝ) (x : UV d): enlarged D d (c • u) x=(↑c:ℂ) • enlarged D d u x := by
  apply Prod.ext
  · change (enlarged _ _ _ _).1=(↑c:ℂ) • ((enlarged _ _ _ _).1); rw [rule0,rule0,smul_zero]
  apply Prod.ext
  · change (enlarged _ _ _ _).2.1 = (↑c:ℂ) • (enlarged _ _ _ _).2.1
    rw [ruleG,ruleG]; unfold YG; rw [Mint.timesL _ _ (leavesG d)]; simp only [LinearMap.smul_apply]; rw [smul_comm]
  apply Prod.ext
  · ext1 i
    change (enlarged _ _ _ _).2.2.1 i = (↑c:ℂ) • (enlarged _ _ _ _).2.2.1 i
    rw [ruleF,ruleF]; unfold EF YF; rw [Mint.timesL _ _ (leavesF d)]; simp only [LinearMap.smul_apply]; rw [smul_comm]
  ext1 i; change (enlarged _ _ _ _).2.2.2 i= (↑c:ℂ) • (enlarged _ _ _ _).2.2.2 i; rw [ruleX,ruleX]; unfold EX YX; rw [Mint.timesL _ _ (leavesX d D.g (D.f i.1)),LinearMap.smul_apply]
lemma fists (u v : Rotors) (x:UV d) : enlarged D d (tick u v) x=enlarged D d u (enlarged D d v x)-enlarged D d v (enlarged D d u x) := by
  apply Prod.ext
  · simp
  simp only [Prod.snd_sub]; apply Prod.ext
  · simp only [Prod.fst_sub,ruleG]; cases D.g
    · simp [activates]; apply Subtype.ext; exact (sub_zero (0:J g)).symm
    simp only [activates,↓reduceIte,one_smul]; exact Mint.circle _ _ (leavesG d) _ _ _
  simp only [Prod.snd_sub]; apply Prod.ext
  · ext1 i; simp only [Prod.fst_sub,Pi.sub_apply,ruleF, EF]; cases D.f i.1
    · simp [activates]; apply Subtype.ext; exact (sub_zero (0:J f)).symm
    simp only [activates,↓reduceIte,LinearMap.smul_apply,one_smul]; exact Mint.circle _ _ (leavesF d) _ _ _
  ext1 i; simp only [Prod.snd_sub,Pi.sub_apply,ruleX]; exact Mint.circle _ _ (leavesX d D.g (D.f i.1)) _ _ _
@[simp] lemma awake (A : Rotors): enlarged D d A (1,0,0,0)=(0: UV d):= by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rw [ruleG]; change activates _ • YG d A 0=0; simp
  · ext1 i; rw [ruleF]; exact map_zero (EF (d:=d) D A _)
  ext1 i; rw [ruleX]; exact map_zero (EX (d:=d) D A _)

lemma marker (q : Signed) (i: FlavorIndex) : (Calibration.rev q i).1=i.1 := by unfold Calibration.rev; split_ifs <;> rfl
lemma tuneF (s : Signed) (p : UV d) (i) : (spinFrame d s p).2.2.1 i=(matter d).moves s (p.2.2.1 (Calibration.rev s i)) := rfl
lemma tuneX (s : Signed) (p : UV d) (i) : (spinFrame d s p).2.2.2 i=(mixed d).moves s (p.2.2.2 (Calibration.rev s i)):=rfl
lemma tuneG (s : Signed) (p: UV d) : (spinFrame d s p).2.1=(gauge d).moves s p.2.1:=rfl
lemma sooner (u : Rotors) (s : Signed) (x : UV d) : enlarged D d (conjS s.ortho u) (spinFrame d s x)=spinFrame d s (enlarged D d u x):=by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [ruleG,tuneG,map_smul]
    congr 1; exact (Mint.faithful _ _ (leavesG d) (gauge d).toCarries (appG d) s u _).symm
  apply Prod.ext
  · ext1 i; simp only [ruleF,tuneF,marker]; unfold EF; simp only [LinearMap.smul_apply,map_smul]; congr 1; exact (Mint.faithful _ _ (leavesF d) (matter d).toCarries (appF d) s u _).symm
  ext1 i; simp only [ruleX,tuneX,marker]; exact (Mint.faithful _ _ (leavesX d D.g (D.f i.1)) (mixed d).toCarries (appX d _ _) s u _).symm
lemma force1 (s : Flavor) (x : UV d) i : (flavors d s x).2.2.1 i= pay (s⁻¹.bit i) (x.2.2.1 (s⁻¹.reprice i)):=rfl
lemma force2 (s : Flavor) (x : UV d) i : (flavors d s x).2.2.2 i= pay (s⁻¹.bit i) (x.2.2.2 (s⁻¹.reprice i)):=rfl
lemma due (u : Rotors) (s : Flavor) (x : UV d) : enlarged D d u (flavors d s x)=flavors d s (enlarged D d u x):=by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext1 i; simp only [ruleF,force1]; rw [show (s⁻¹.reprice i).1=i.1 from rfl]; cases s⁻¹.bit i <;> simp only [pay_false,pay_true,map_neg]; exact map_neg (EF D u i.1) (x.2.2.1 _)
  ext1 i; simp only [ruleX,force2]; rw [show (s⁻¹.reprice i).1=i.1 from rfl]; cases s⁻¹.bit i <;> simp only [pay_false,pay_true,map_neg]; exact map_neg (EX D u i.1) (x.2.2.2 _)
lemma realG (u : Rotors) (x: UV d) : enlarged D d u (shade d x)= shade d (enlarged D d u x):=by
  apply Prod.ext
  · exact (map_zero bar).symm
  apply Prod.ext
  · have he (y : UG d): flipT (gauge d) (YG d u y)=YG d u (flipT (gauge d) y) := Subtype.ext (Mint.cReal _ _ (leavesG d) u y (flipT (gauge d) _) rfl).symm
    rw [ruleG]; change activates _ • _= flipT _ (enlarged _ _ _ _).2.1
    rw [ruleG,LinearMap.map_smulₛₗ,he]; rw [show bar (activates D.g)=activates D.g from by cases D.g <;> simp [activates]]; rfl
  apply Prod.ext
  · ext1 i
    have he (y : UF d) : flipT (matter d) (YF d u y)=YF d u (flipT (matter d) y):=Subtype.ext (Mint.cReal _ _ (leavesF d) u y (flipT (matter d) _) rfl).symm
    rw [ruleF]; change _= flipT (matter d) ((enlarged D d u x).2.2.1 i); rw [ruleF]; unfold EF; simp only [LinearMap.smul_apply,LinearMap.map_smulₛₗ,he]; rw [show bar (activates (D.f i.1))=activates (D.f i.1) by cases D.f i.1 <;> simp [activates]]; rfl
  ext1 i; rw [ruleX]; change _= flipT (mixed d) ((enlarged D d u x).2.2.2 i); rw [ruleX]
  exact Subtype.ext (Mint.cReal _ _ (leavesX d _ _) u (x.2.2.2 i) (flipT (mixed d) _) rfl)
end Law
end YM.GaugeFieldConstruction.Stage
