import YM.SU5.WakeInvestment.Shuttle
import YM.SU5.Celeste.Custodian
import YM.SU5.FiniteGaugeData.Tower.Chimes
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Shuttle
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexOrder
open Fock Cube Lat Tenant Tulip Scree Skye
open Buffered Afterglow Journey Buffered.Afterglow.Tower Ballad SitSpin SpinReceipt Tapestry
open Lifted Onyx
open YM.Stationary (Gaia)
open Py Preparation YM.Pressure
open Phase Rush Scroll Peaks Spire
open Lamour Lamour.Bridge Lamour.Bridge.Celeste Morn
attribute [local instance] opCStarAlgebra
open Py.Rate.LocalLimit.Papal (Weaver household)
variable {P:Preparation}{A v E:ℝ}{I:Type*}[Fintype I] (u:I→Lead.Clan) (G:List I)(s:ℕ)
abbrev OPlus (P:Preparation)(z:ℕ→ I→ Cover)(A:ℝ)(n s:ℕ):= forward (z s) P A n s
abbrev OMinus (P:Preparation)(z:ℕ→ I→ Cover)(A:ℝ)(n s:ℕ):= Shuttle.flip ∘ OPlus P z A n s
abbrev twins : List (I ⊕ I):= G.map Sum.inl ++ G.map Sum.inr

variable (z:ℕ→ I→ Cover)
local notation "Tδ" s:max => pillJar P u (z s) 0 A s G
local notation "TPlus" n:max s:max => pillJar P u (OPlus P z A n s) 0 A s G
local notation "TMinus" n:max s:max => pillJar P u (OMinus P z A n s) 0 A s G
lemma vocalP(P:Preparation)(A:ℝ) : Voice (pillJar P u (z s) 0 A s G) (lay (z s) G):=by rw [pillJar_read]; exact (SitSpin.reader_voice u (z s) _ _ G).hushed _
lemma vocal_two (z:ℤ)(F G:Papal.Weaver):fluent 3 z (F*G)= (fluent 3 z F)*(fluent 3 z G):=funext fun N=>funext fun x=> theta_mul .. -- B dummy rm
lemma movedJar (z:ℤ)(x:I→ Cover): fluent 3 z (pillJar P u x 0 A s G)=pillJar P u ((plane 3 z).flee ∘ x) 0 A s G:=by
 induction G with
 | nil=> funext n X; exact theta_one _
 | cons i G h=> rw [show pillJar _ _ x _ _ _ (i::G)=_ from (show pillJar P u x 0 A s (i::G)=pill P A s (u i) (x i) 0 * pillJar P u x 0 A s G from rfl), vocal_two, h]; funext n y; change reflMark 3 z (pill P A s (u i) (x i) 0 n) y * _= (((pill P A s (u i) _ 0 n) y)* _); rw [pill_theta]; try rfl
lemma carry_positive (n:ℕ): takeoff P.block (Tδ s) 3 (kroll P A n s) = TPlus n s:=by
 unfold takeoff traction; rw [movedJar,movedJar]; exact congrArg (fun i=> pillJar P u i 0 A s G) (funext fun j=> commute_f ..)
lemma carry_negative (n:ℕ): fluent 3 0 (takeoff P.block (Tδ s) 3 (kroll P A n s))= TMinus n s:=by rw [carry_positive,movedJar]
lemma carry_both (n:ℕ): father P.block 3 (Tδ s) (kroll P A n s)= pillJar P (Sum.elim u u) (troupe (z s) P A n s) 0 A s (twins G):=by unfold father; rw [carry_negative,carry_positive]; simp only [pillJar,twins,List.map_append,List.prod_append,List.map_map]; rfl

variable {ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (H:Real.exp 1≤ P.x)
variable {φ μ π κ:ℕ→ℕ} {E' : ℕ→ Buffered.Family (tent Y H) →ℂ}{X:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
variable {D₀:ℕ→Buffered.Family (tent Y H)→Buffered.Family (tent Y H)} (V:Universal Y H φ μ X E') (Q:Coherent (i:=φ) (k:=μ) (E:=E') Y H D₀ π κ)
local notation "CC" => household (tent Y H)
include V
lemma opp_note (S:Finset Cover)(F: Papal.Weaver)(t:Voice F S){n:ℕ}(h:Tower.region 3 0 (tent Y H).ℓ (onFlight P.block S 3 n)) : E' s (CC (fluent 3 0 (takeoff P.block F 3 n)))=star (E' s (CC F)) :=by
 let U := takeoff P.block F 3 n; have hp := SWay Y H V s 3 (n:ℤ) (aux_test ((t.1.narrow (tent Y H)).widen))
 let G:= CC F; let K:=tent Y H; let Z:= Heat.gaugeShift P.block n; change E' s (CC U)=E' s G at hp; let z:= Heat.gaugeShift P.block (0:ℤ)
 have he: z=0:=by unfold z Heat.gaugeShift; simp
 change E' s (Buffered.Afterglow.Tower.mirror K 3 0 (CC U))=star (E' s G); rw [←hp,←he]; apply mirror_band Y H V s 3 0; exact ⟨onFlight P.block S 3 n, (t.tract 3 Z).1.narrow K|>.widen, he.symm ▸ h⟩

-- subtract a common bill. reflection comparison remains through the norm invoice, including if f has issued arbitrary number of parts in this computation.
def changeT (F:Papal.Weaver)(w:ℂ) := F-w • (1:Papal.Weaver)
omit V
lemma cform (n:ℕ)(b:ℂ)(F:Papal.Weaver):
    let x:= takeoff P.block F 3 n; let y:=fluent 3 0 x
    father P.block 3 (changeT F b) n=father P.block 3 F n-b • y-star b • x+ (star b*b) • 1:=by
 intro x y; have h:∀ (a:ℤ)(F:Papal.Weaver)(b:ℂ), fluent 3 a (changeT F b)=fluent 3 a F-star b • 1:= fun a F b=>funext fun N=>funext fun i=>by
    let U:= carR 3 a N; let V:= reflFields 3 a i; change theta U (F N V-b • 1)=theta U (F N V)- star b • 1; rw [theta_sub,theta_smul,theta_one]
 let g:= Heat.gaugeShift P.block n; have e: takeoff P.block (changeT F b) 3 n=changeT x b:=by
    change fluent _ _ (fluent _ _ (changeT F b))= _; rw [h]; change fluent 3 g (changeT (fluent 3 0 F) (star b))= _; rw [h,star_star]; rfl
 unfold father; rw [e,h]; change (y-star b • 1)*(x-b • 1)=y*x-b • y-star b • x+(star b*b) • 1; simp only [mul_sub,sub_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_sub,smul_smul,mul_comm b (star b),mul_one,one_mul]; abel
include V
lemma cInvoice (b:ℂ)(S:Finset Cover)(F:Papal.Weaver)(t:Voice F S){n:ℕ}(h:Tower.region 3 0 (tent Y H).ℓ (onFlight P.block S 3 n)) :
    E' s (CC (father P.block 3 (changeT F b) n))=E' s (CC (father P.block 3 F n))-b*star (E' s (CC F))-star b*E' s (CC F)+ star b*b:=by
 rw [cform]; let J:= Heat.gaugeShift P.block n; let X:= t.tract 3 J; let U:= takeoff P.block F 3 n; let x:= CC U; let G:=CC F; let f:= CC (father P.block 3 F n); let y:= CC (fluent 3 0 U);
 have a:TestFamily (tent Y H) true x:= aux_test ((X.1.narrow _).widen); have a':TestFamily (tent Y H) true y:= aux_test (((X.turn 3 0).1.narrow _).widen);
 have hx(F G:Buffered.Family (tent Y H))(p:TestFamily (tent Y H) true F)(t:TestFamily (tent Y H) true G): TestFamily (tent Y H) true (F-G):= by rw [sub_eq_add_neg,←neg_one_smul ℂ G]; exact p.add (t.scale _)
 have hf:TestFamily (tent Y H) true f:= a'.mul a
 change E' s (f-b • y-star b • x+(star b*b) • 1)=_; rw [E_add Y H V s (hx _ _ (hx _ _ hf (a'.scale b)) (a.scale _)) (TestFamily.oneT.scale _),E_sub Y H V s (hx _ _ hf (a'.scale b)) (a.scale _),E_sub Y H V s hf (a'.scale _),E_scale Y H V s a',E_scale Y H V s a,E_scale Y H V s TestFamily.oneT,E_unit Y H V s,mul_one,show E' s x=E' s G from SWay Y H V s 3 (n:ℤ) (aux_test ((t.1.narrow _).widen)), show E' s y=_ from opp_note s Y H V S F t h]
open SpinReceipt
variable (y:I→Gaia) (J:Investment P E v)(L_:Dispatchers P)(K:Meritorious P) (p:0<A)(h:∀ i, Appoint P A (fun s=> z s i) (y i))(f:∀ i j,y i=y j→∀ᶠ s:ℕ in atTop, z s i=z s j)
local notation "u'" n:max => (fun i=> gait P (y i) n) -- parser tricky
include V Q J L_ K p h f
variable {z} (n_:ℕ)
local notation "WH" => wakeSum y G u 0
abbrev oppCnt (P:Preparation)(y:I→Gaia)(n:ℕ):= Shuttle.opposite ∘ fun i=> gait P (y i) n
lemma phasePois (n:ℕ)(t:∀ i,0 < gait P (y i) n 3):
    wakeSum (Shuttle.opposite ∘ y) G u 0=star (wakeSum y G u 0):=by
 let YP:=u' n; let w:= Shuttle.opposite ∘ y; let o:= oppCnt P y n; let S(s:ℕ)(i:I):= OMinus P z A n s i
 have hv(i): Appoint P A (fun s=> S s i) (o i):= (troupe_loan p h f n t).1 (Sum.inl i)
 have hp(i j:I)(k:o i=o j):∀ᶠ s in atTop,S s i=S s j:= (troupe_loan p h f n t).2 (Sum.inl i) (Sum.inl j) k
 have hx: wakeSum o G u 0=wakeSum w G u 0:=by
    apply Eq.symm; have he:= SpinReceipt.wakePower o w 1 zero_lt_one (fun i j=>?_ ) G u (0:I→Twah.DirSpin)
    · simpa using he
    · unfold o w oppCnt; simp only [Function.comp_apply,flip_d, gait_d,one_smul] -- name ambiguity
 -- extract E_s mirror → star from *these* appointments. need pose carries U & phases.
 have he:= revenue_limit Y u G (0:I→ Twah.DirSpin) V Q J L_ K p h f
 let A0 s:= insideJar P (tent Y H) u G (z s) 0 A s; let B0 s:= insideJar P (tent Y H) u G (S s) 0 A s
 have hy: Tendsto (fun s:ℕ=> E' s (B0 s)) atTop (𝓝 (star (WH))):=by
    apply he.star.congr'; filter_upwards [to_zone p h t G (tent Y H).ℓ] with s p'; change star (E' s (CC (Tδ s)))= E' s (CC (TMinus n s)); rw [←carry_negative]; exact (opp_note s Y H V (lay (z s) G) (Tδ s) (vocalP u G s z P A) p').symm
 exact hx ▸ tendsto_nhds_unique (revenue_limit Y u G (0:I→Twah.DirSpin) V Q J L_ K p hv hp) hy

lemma father_far (n:ℕ)(t:∀ i,0< gait P (y i) n 3) :
    Tendsto (fun s:ℕ=> E' s (CC (father P.block 3 (changeT (Tδ s) WH) (kroll P A n s)))) atTop (𝓝 (wakeSum (dualC (u' n)) (twins G) (Sum.elim u u) 0-star (WH)* WH)):=by
 let w:= WH; let X0 s:= CC (Tδ s); let F(s:ℕ):= E' s (X0 s)
 have hf:Tendsto F atTop (𝓝 w):=revenue_limit Y u G _ V Q J L_ K p h f
 obtain ⟨t,p'⟩:= troupe_loan p h f n t -- shadow t rename
 let A0:= u' n; let W:= wakeSum (dualC (A0)) (twins G) (Sum.elim u u) 0; let Y0 s:= E' s (CC (father P.block 3 (Tδ s) (kroll P A n s)))
 have ht:Tendsto Y0 atTop (𝓝 W):=by unfold Y0; simp_rw [carry_both]; exact revenue_limit Y (Sum.elim u u) (twins G) (0:(I⊕I)→Twah.DirSpin) V Q J L_ K p t p'
 have he:= (((ht.sub (hf.star.const_mul w)).sub (hf.const_mul (star w))).add_const (star w*w)); rw [show W-w*star w-star w*w+ star w*w=W-star w*w by ring] at he; apply he.congr'
 filter_upwards [to_zone p h (n:=n) ‹∀ i,0<(A0 i) 3› G (tent Y H).ℓ] with s p0
 exact (cInvoice s Y H V w _ _ (vocalP u G s z P A) p0).symm

lemma saba (χ:ℝ)(b:0<χ) : ∃ n:ℕ,(∀ᶠ s:ℕ in atTop,Tower.region 3 0 (tent Y H).ℓ (onFlight P.block (lay (z s) G) 3 (kroll P A n s)))∧∀ᶠ s:ℕ in atTop,
    ‖E' s (CC (father P.block 3 (changeT (Tδ s) WH) (kroll P A n s)))‖<χ:=by
 let w:= WH; let x:=Shuttle.opposite∘ y; let u₀(n:ℕ):= u' n; let v₀(n:ℕ):=Shuttle.opposite∘u₀ n
 have hv(n:ℕ)(i j:I): u₀ n i-u₀ n j=y i-y j:= gait_d ..
 have ht(n:ℕ)(i j:I): v₀ n i-v₀ n j=x i-x j:=by unfold v₀ x; simp only [Function.comp_apply,flip_d,hv]
 have hp:∀ᶠ n:ℕ in atTop,∀ i,0 < (gait P (y i) n) 3:= Filter.eventually_all.mpr fun i=> (gait_up P (y i)).eventually_gt_atTop 0
 obtain ⟨n,v⟩:=hp.exists
 let U:= wakeSum x G u 0; let Q0 (n):= wakeSum (dualC (u₀ n)) (twins G) (Sum.elim u u) 0
 have hu:Tendsto Q0 atTop (𝓝 (U*w)):= furthest G G u u x y v₀ u₀ ht hv (fun i j=>foreign P (y i) (y j))
 obtain ⟨m,g,z'⟩:= (((Metric.tendsto_nhds.mp hu χ b)).and hp).exists; rw [dist_eq_norm,show U=star w from phasePois u G Y H V Q y J L_ K p h f n v] at g; exact ⟨m,to_zone p h z' G (tent Y H).ℓ,(father_far u G Y H V Q y J L_ K p h f m z').norm.eventually (gt_mem_nhds g)⟩ -- Q
-- expose axiom test at manuscript (parallel with Leg orientation qualifiers)
#print axioms cInvoice
#print axioms saba
end YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Shuttle
