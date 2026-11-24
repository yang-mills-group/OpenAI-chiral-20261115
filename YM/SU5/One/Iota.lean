import YM.SU5.One.Overture

/-!
# Graded reflection for Course/Universal
We can indeed insert odd chiral marks at each observing level (through any
allowed number of levels). Entirely on the original Y and Universal. E on odd
must be extended by zero; the true test here is before restricting to even/odd
summands, (need that too; do positivity, application next CP). This is NOT using a fresh subsequence.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry Tapestry.Altitude Spark PhaseChoice

section worlds
-- Adapt CF/Buffered/DonorGram, FiniteGaugeData/Tapestry/{Levels,Junction}, Selected/FullLattice
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree RG Spark RP Gloss Branch Reflect Window Vale Girt
open Py (Vestal Cape)
open Reed (Fine think)
open Advance Heat

variable {m B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ}
variable (P : Grasp Y B e) (X : Vestal m B L) (R : Cape m B L) (q : Chi) (d : ℝ)
variable (n : ℕ) (Q : ℕ → Haro.SpaceM)
variable (A : Steps m B L) {D J:ℕ} (v : Stencil.LaurentRadius j L D) (T : Granted P X R q d n Q A J)
include T v
local notation "rise₁" => nextMark (j:=j) (ho:=ho) X R q d Q A
lemma single_money {k : ℕ} {f : Mark (cell m B L k)} {b : Bool} (h : AtSupport b univ f) (u : k<n) : markedRead f (R k) (denZ (X k) P (R k)) = markedRead (rise₁ k f) (R (k+1)) (denZ (X (k+1)) P (R (k+1))) := by
  obtain ⟨g⟩:= T.grant k u
  exact identity_step _ g _ (T.branch k u) (T.aligned k u) (Q k) ho v h (((measurePreserving_fst (μ:=prior group (More (cell m B L k))) (ν:=depot (cell m B L k))).quasiMeasurePreserving.ae ((T.noTies k u.le) _)).mono fun x h=> T.wears _ u x h)
end worlds
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E) (s:ℕ)
local notation "K"=>tent Y H

section measure
variable (i' k':ℕ)
local notation "L"=> Λ.R.L
local notation "B"=> Λ.block
local notation "C"=> (Y.voyage i').CapeT
local notation "N"=> Y.uv k'
local notation "Ω" i:max => side Y i s
local notation "Z"=> ((Y.voyage i').X (Y.uv k'))
local notation "σ"=> Ω i'
variable {b d:Bool}(p:Satin.PairIdx Y s i' k') {f : Mark (side Y i' s)}
include p
lemma ascendTurnB (g:Axis)(z:ℤ)(f' : AtSupport b univ f): ascender Y s i' k' (reflMark g z f)=reflMark g ((Λ.R.L.val:ℤ)*z) (ascender Y s i' k' f):=
 rising (Vale.apt (Y.ir i') Λ.block Λ.R.L s) (patternA Y s i' k') Λ.K.j (patternQ Y s i' k').val _ Λ.R.odd_side _ _ (patternβ Y s i' k') _ g z ((fullness Y i' k' p.1).cap_grant.aligned s p.2) f' ((fullness Y i' k' p.1).cap_grant.branch s p.2) ((Y.voyage i').ownership s).paid (Journey.legal Λ) (Tapestry.threshold Y).1 (Tapestry.threshold Y).2
lemma ascendSepB {F:Mark σ}
    {U' V' : Support (More σ)}(f': AtSupport b U' f)(F': AtSupport d V' F)
    (r:∀ x∈ U',∀ y∈ V', 2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)<separation x y) : ascender Y s i' k' (f*F)=ascender Y s i' k' f*ascender Y s i' k' F:=
 separated_mult (Vale.apt ..) (patternA Y s i' k') Λ.K.j (patternQ Y s i' k').val _ Λ.R.odd_side _ _ (patternβ Y s i' k') _ (Journey.legal Λ) ((Y.voyage i').ownership s).paid.bill ((fullness Y i' k' p.1).cap_grant.branch s p.2) (Tapestry.threshold Y).1 (Tapestry.threshold Y).2 f F f' F' (tissue Y i' s) r
lemma partakeB(h:AtSupport b univ f) : Journey.compass Y i' k' s f=Journey.compass Y i' k' (s+1) (ascender Y s i' k' f):=by
  unfold Journey.compass; rw [single_money Λ.U (Z).gram C Chi.canonical Λ.J.d (Y.uv k') (Z).wave (steps Λ.V (Y.ir i') Λ.block (Y.uv k')) (Journey.legal Λ) (fullness Y i' k' p.1).cap_grant h p.2, (Z).balance s p.2.le,← (Z).balance (s+1) p.2]
omit p
lemma heatCollectorGrade {a:Axis}{z:ℤ} {y:Mark ((K).c (momentm Y i' s))} (h:AtSupport b (band ((K).c (momentm Y i' s)) a (gaugeShift Λ.block z) (K).ℓ) y) (u:Ferry Y s i' k') :
   0 ≤ collector Y H i' k' u.depth s (chord b • (reflMark a (gaugeShift Λ.block z) y*y)) := by
  let X:= (Y.voyage i').Q k' u.depth
  let w:= partitionZ (X.gram s) Λ.U (C s)
  let TileP:= denZ (X.gram s) Λ.U (C s)
  have he:0≤w:=by
    have hp:= throbbing Y i' k' u.depth s u.enters a z 1 (AtSupport.oneM (band σ a (Heat.gaugeShift B z) (reserve Λ l)))
    rw [mul_one,show reflMark a (Heat.gaugeShift B z) (1:Mark σ)=1 from funext fun _=> Fock.theta_one _,markvac] at hp
    exact hp
  unfold collector solder
  refine div_nonneg ?_ he
  let r:=terrain Y H (Y.ir i') s
  rw [show Journey.send Y H i' s (chord b • (reflMark a (gaugeShift Λ.block z) y*y))=arrange _ _ r (chord b • (reflMark a (gaugeShift Λ.block z) y*y)) from (arranged ..).symm,map_smul,displayMult,displayRef]; have t:= fullness Y i' k' u.depth
  exact onward_grade _ _ _ _ _ _ _ _ (Journey.legal Λ) Λ.R.coarse t.warm_grant (fun i _=> tissue Y i' i) (prepared Λ l) t.heat.choose _ s u.enters _ _ (bandCast a (gaugeShift B z) r h)
where bandCast {J P':Side}(a:Axis)(s':ℤ){M:ℕ}{f:Mark J}(t:J=P')(h:AtSupport b (band J a s' M) f): AtSupport b (band P' a s' M) (arrange J P' t f):= by subst J; exact h
end measure

section zero
variable {N : Side}{W : UNI (Single N)}(w: W.val = -1)
include w
lemma spot_turn {T:FC (Single N)}{S:Finset (Single N)} {b:Bool}(t: Sector S b T): twist (quantU W) T=if b then -T else T:=by
 rw [show W=phaseU (-1) (by simp) from Subtype.ext <| (w.trans (neg_one_smul ℂ (1:Op (Single N))).symm), Sector.grade_diag t]; cases b <;> simp

omit w
-- compose two mirrors dotted (2π spin rep) without moving gauge. Compare prep.
lemma turnedSpot (i:Axis) : ∃ S: UNI SpinIdx, JetS 1 false false S ∧ (prepU (lagX 0) S inert N).val = -1:=by
 let S:=pinLift i*pinLift i
 have hg:= jet_add false true true (Signed.mirror i) (Signed.mirror i) _ _ (mirrorX i) (mirrorX i)
 have ht:Signed.mirror i * Signed.mirror i=1:=by nth_rw 1 [← Signed.mirror_inv i]; exact inv_mul_cancel _
 rw [ht] at hg
 refine ⟨S,hg,?_⟩; have hx:= carR_square (n:=N) i 0
 change (carR i 0 N * carR i 0 N).val= -1 at hx; rw [carR,kio,plane_join] at hx; simpa only [_root_.sub_self,zero_smul] using hx

local notation "Π" x:max=> inner ℂ (Dial.mateK N) x
lemma starBlank (Z:Wave (Single N)) (S:UNI SpinIdx) (h:JetS 1 false false S)
    (u:(prepU (lagX 0) S inert N).val= -1) (v: Spire.arum (prepU (lagX 0) S inert N) false false (Dial.mateK _) Z=Z) (f:FC (Single N)){U:Finset (Single N)}(t:Sector U true f):Π (acts f Z)=0:=by
 let A:=lagX (0:Cover); let M:=prepU A S inert N
 let K':= Spire.arum M false false (Dial.mateK _)
 have hs: Sea (cutM (Tset N)) (Dial.mateK _):=(touchP N) ▸ Dial.tickB N
 have hx:= tickR A inert S (show JetS A.s false false S from h) N
 have he : Π (acts f Z) = Π (acts (-f) Z):=by
   rw [show -f=Spire.tourP M false false f from (spot_turn u t).symm]
   calc
      Π (acts f Z)=inner ℂ (K' (Dial.mateK N)) (K' (acts f Z)):= (arum_globe M false false (Tset _) hs hx _ _).symm
      _= _:= by unfold K'; rw [arum_self (q:=Dial.mateK N) M false false (Tset _) hs hx, arum_act M false false, show arum M false false (Dial.mateK N) Z=Z from v]
 rw [act_neg,inner_neg_right] at he; exact (mul_eq_zero.mp ((two_mul (Π (acts f Z))).trans (neg_eq_iff_add_eq_zero.mp he.symm))).resolve_left (by norm_num)


variable (i' k':ℕ)
local notation "N₁"=> Y.uv k'
local notation "C"=> (Y.voyage i').CapeT
local notation "Y₁"=>side Y i' N₁
lemma spot_none {f:Mark Y₁}(h:AtSupport true univ f): Journey.compass Y i' k' N₁ f=0 := by
 let M:= (((Y.voyage i').X (Y.uv k')).gram N₁); let T:= denZ M Λ.U (C N₁)
 change (∫ x:Orbit Y₁, letterRead (f (drawn (C N₁) x)) (T x) ∂Scree.city Y₁) / _=0
 obtain ⟨S,hs,eq⟩:= turnedSpot (N:=Y₁) 0
 have ht (x: Orbit Y₁) : letterRead (f (drawn (C N₁) x)) (T x)=0:=by
   refine starBlank (T x) S hs eq ?_ _ (h.allV _).sector
   unfold T M; rw [Y.whole]
   exact (tenor Y i' k' x.1 (lagX 0) S hs).trans (congrArg _ (show stir (xtra false) (lagX 0) x.1=x.1 from Nacre.blank _))
 simp_rw [ht, integral_zero]
 rw [zero_div]

lemma paysNone {U:Finset Cover}{F:Mark (side Y i' s)}(p:Pay Y s i' k')(h:AtSupport true (Satin.region U (side Y i' s)) F): Journey.compass Y i' k' s F=0:=by
 suffices e:∀ i:ℕ,∀{s:ℕ},∀(_e:s+i=N₁){U:Finset Cover}{F:Mark (side Y i' s)},AtSupport true (Satin.region U (side Y i' s)) F→ Journey.compass Y i' k' s F=0 from e (N₁-s) (by have t:=p.2; omega) h
 intro i; induction i with
 | zero=>intro s e U F hp; rw [Nat.add_zero] at e; subst s; exact spot_none Y i' k' (hp.mono (subset_univ _))
 | succ i ih=> intro s e U F hp; have w:Satin.PairIdx Y s i' k':=⟨p.1,by omega⟩; rw [partakeB Y s i' k' w (hp.mono (subset_univ _))]; exact ih (by omega) (ascendSupport Y s i' k' U w hp)
end zero
section algebra
variable {K':Calibration}

def homTest (L:Calibration) (b:Bool) : Submodule ℂ (Family L) where
  carrier:= {f|∃ S:Finset Cover, InTest L true S b f}
  add_mem' := by rintro F G ⟨S,h⟩ ⟨T,u⟩; exact ⟨S∪T,.add (h.mono Finset.subset_union_left) (u.mono subset_union_right)⟩
  smul_mem' a _:=by rintro ⟨S,h⟩; exact ⟨S, .smul a h⟩
  zero_mem':=⟨∅,.zero⟩

def gradeFlank (L:Calibration)(d:Bool)(a:Axis)(z:ℤ): Submodule ℂ (Family L) where
  carrier:= {f|∃ S:Finset Cover, InTest L true S d f ∧ Tower.region a z L.ℓ S}
  add_mem' := by rintro F G ⟨S,h,v⟩ ⟨T,u,p⟩; exact ⟨S∪T,.add (h.mono Finset.subset_union_left) (u.mono subset_union_right),fun i w=> (mem_union.mp w).elim (v i) (p i)⟩
  smul_mem' a _:=by rintro ⟨S,h,v⟩; exact ⟨S, .smul a h,v⟩
  zero_mem':=⟨∅,.zero,by simp [Tower.region]⟩

lemma flank_graded {a:Axis}{z:ℤ}{b} : gradeFlank K' b a z ≤ homTest K' b:= by
  rintro _ ⟨S,h,v⟩; exact ⟨S,h⟩
lemma homMirror {a:Axis}{z:ℤ}{b:Bool}{f:Family K'} (h:f∈homTest K' b) : mirror K' a z f∈ homTest K' b:= by obtain ⟨S,x⟩:=h; exact ⟨_,axial _ _ _ x⟩
lemma homCross {a b:Bool}{f g:Family K'}(h:f∈homTest K' a)(t:g∈homTest K' b): f*g∈ homTest K' (a.xor b):=by
  obtain ⟨S,x⟩:=h; obtain ⟨T,y⟩:=t; exact ⟨S∪T,(x.mono subset_union_left).mul (y.mono subset_union_right)⟩
lemma hom0 {f:Family K'}: f∈homTest K' false↔ TestFamily K' true f:=⟨fun ⟨_,p⟩=> aux_test p, fun h=> h.paid⟩
lemma firmZero {b:Bool}{f:Family K'} (h:f∈homTest K' b)(t:f∈homTest K' (!b)): f=0:=by
  obtain ⟨S,v⟩:=h; obtain ⟨T,w⟩:=t
  funext n X; change f n X=0; let A:=f n X
  have hp:= Fock.Sector.grade_diag ((v.support n).allV X).sector
  have ht:= Fock.Sector.grade_diag ((w.support n).allV X).sector
  have he:=hp.symm.trans ht; cases b
  · simp at he; have hr : (2:ℂ) • A=0:=by rw [show (2:ℂ)=1+1 from by norm_num,add_smul,one_smul]; exact neg_eq_iff_add_eq_zero.mp he.symm
    exact (smul_eq_zero.mp hr).resolve_left (by norm_num)
  · simp at he; have hr : (2:ℂ) • A=0:=by rw [show (2:ℂ)=1+1 from by norm_num,add_smul,one_smul]; exact neg_eq_iff_add_eq_zero.mp he
    exact (smul_eq_zero.mp hr).resolve_left (by norm_num)
end algebra

section grade
variable (a:Axis)(z:ℤ)(b:Bool)
local notation "Z₁"=> Heat.gaugeShift Λ.block z
local notation "W"=>gradeFlank K b a Z₁
local notation "R"=> mirror K a Z₁

def badge (a:Axis)(z:ℤ)(f g:Family (tent Y H)): Family (tent Y H):= Reflect.chord b • (mirror K a z f*g)
local notation "μ"=> badge Y H b a Z₁ -- binder order?

lemma stamps {f g:Family K}(h:f∈homTest K b)(t:g∈homTest K b): μ f g ∈ homTest K false := (homTest _ _).smul_mem _ (by simpa using homCross (a:=b) (homMirror (a:=a) (z:=Z₁) h) t)
lemma meets_test (f g:W): TestFamily K true (μ f.val g.val) := hom0.mp <| stamps Y H a z b (flank_graded f.property) (flank_graded g.property)
include V
lemma printed_positive (f:W): 0 ≤ E s (μ f.val f.val):=by
  obtain ⟨S,p,h⟩:= f.property
  have hv:= warm_limit Y H V s (meets_test Y H a z b f f)
  apply ge_of_tendsto hv.periods
  filter_upwards [((momentum Y s).comp V.pick.grow_i.tendsto_atTop).eventually (recedes (tent Y H) h)] with r w
  apply ge_of_tendsto (hv.inner (i r))
  filter_upwards [V.pick.pass Y H s _] with t u; unfold hot; rw [dif_pos u.depth]
  exact heatCollectorGrade Y H s _ _ ((p.support _).mono w) u

def gradeForm : W→ₗ⋆[ℂ] W→ₗ[ℂ] ℂ where
 toFun f:= {
    toFun:= fun g=> E s (μ f.val g.val)
    map_add' := fun x y=> by unfold badge; rw [AddSubmonoid.coe_add,mul_add,smul_add]; exact E_add Y H V s (meets_test Y H a z b f x) (meets_test Y H a z b f y)
    map_smul' := fun c x=> by unfold badge; rw [Submodule.coe_smul,Algebra.mul_smul_comm,smul_comm]; exact E_scale Y H V s (meets_test Y H a z b f x) c }
 map_add' f g:= LinearMap.ext fun x=>by change E s _= E s _+E s _; unfold badge; rw [AddSubmonoid.coe_add,mirror_plus,add_mul,smul_add]; exact E_add Y H V s (meets_test Y H a z b f x) (meets_test Y H a z b g x)
 map_smul' c f:= LinearMap.ext fun x=>by change E s _=star c*E s _; unfold badge; rw [Submodule.coe_smul,mirror_scale,Algebra.smul_mul_assoc,smul_comm]; exact E_scale Y H V s (meets_test Y H a z b f x) _

omit V
abbrev Grade(n:Bool):= ↥(gradeFlank K n a Z₁)

include V
/-- Pair against even+odd input. Use exactly theta with i phase; assert positivity on actual E and relation to sharp data before splitting by grade. -/
noncomputable def part_two : Grade Y H a z false × Grade Y H a z true→ₗ⋆[ℂ] Grade Y H a z false × Grade Y H a z true→ₗ[ℂ] ℂ :=
 have f := LinearMap.fst ℂ (Grade Y H a z false) (Grade Y H a z true); have g:=LinearMap.snd ℂ (Grade Y H a z false) (Grade Y H a z true)
 -- use explicit for now
 { toFun:= fun A=> (gradeForm Y H V s a z false A.1).comp f + (gradeForm Y H V s a z true A.2).comp g
   map_add':= fun x y=> LinearMap.ext fun z'=> by simp only [LinearMap.add_apply,Prod.fst_add,Prod.snd_add,map_add,LinearMap.comp_apply]; abel
   map_smul' := fun c x=> LinearMap.ext fun z'=> by simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.add_apply]; change ((gradeForm Y H V s a z false) (c • x.1)) _ + ((gradeForm Y H V s a z true) (c • x.2)) _=_; simp only [map_smulₛₗ, LinearMap.smul_apply, smul_add] }
lemma part_two_kernel {T:Type*}[Fintype T] (f:T → Grade Y H a z false × Grade Y H a z true): Matrix.PosSemidef (Matrix.of fun i j=> part_two Y H V s a z (f i) (f j)):=halfSpaceKernel _ (fun u=> add_nonneg (printed_positive Y H V s a z false u.1) (printed_positive Y H V s a z true u.2)) f
end grade
end YM.CF.Buffered.Afterglow.Tower.One
