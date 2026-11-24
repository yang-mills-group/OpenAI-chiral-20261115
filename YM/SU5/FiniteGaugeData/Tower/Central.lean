import YM.SU5.FiniteGaugeData.Tower.Satchel
/-!
# The satchel terminal seam: one meeting of a long train on the actual torus

Need no extra alignment of the opposite reflection plane. Test in warmed RP at
this chamber; reservations at BOTH positions check in native arcs, including
transverse support for the empty-endpoint read. Endpoints need pair price in
Tandem (they remain 2 clusters, not 1). Mark x beyond 2w clearance; arbitrary
extra translation c of train maintained as integer alignment.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 240000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat Analysis
section seam
variable {K:Calibration}{m:Side}{L:Scree.Loom (K.c m)}{Y:Mark (K.c m) →ℂ}{D:ℝ}(p:Metered K m L Y D)
local notation "N"=> K.c m
variable (j:Axis)(w:ℤ){f x:Family K}
local notation "U" i:max=> relocate K j i
local notation "R" i:max=> mirror K j i
local notation "b₀"=>ruler K.B
local notation "r" i:max=>gaugeT K i
local notation "J"=>lace K j w
local notation "O"=>plow K j
variable (v:ℤ)(n:ℕ)
noncomputable def orbitPlus (x:Family K):Family K:=(U (v+w*n)) x
noncomputable def orbitMinus (x:Family K):Family K:=(U (v-w*n)) ((R 0) x)
noncomputable def sensors (x:Family K):Family K:=orbitMinus j w v n x * orbitPlus j w v n x
local notation "S₁"=> sensors j w v n x
local notation "F₁"=> chambers j w v f 1 n

lemma dividing (h:TestFamily K true f)(k:TestFamily K true x):chambers j w v f x n=S₁*F₁:=by
 unfold chambers sensors orbitMinus orbitPlus
 set Y:=J f 1 n
 have hp:= unlace K j w h k n
 have hi:= lace_paid K j w h (aux_test (S:=∅) InTest.one) n
 rw [hp,mirror_times,mirror_relocate K j (w*n) 0 k]; repeat' rw [relocate_mul]
 rw [relocate_sums K j _ _ k,relocate_sums K j _ _ (reflect_ok K j _ k), ←sub_eq_add_neg]
 let A:=(U v) ((R 0) Y); let C:=(U v) Y; let B:=(U (v-w*n)) ((R 0) x); let D:=(U (v+w*n)) x
 change A * B * (C*D)= B*D*(A*C)
 have heAB:A*B=B*A:=even_tests K (move_ok K j v (reflect_ok K j _ hi)) (move_ok K j _ (reflect_ok K j _ k))
 have heADC:(A*C)*D=D*(A*C):=even_tests K ((move_ok K j v (reflect_ok K j _ hi)).mul (move_ok K j _ hi)) (move_ok K j _ k)
 rw [heAB,mul_assoc B A,←mul_assoc A C,heADC,mul_assoc]

noncomputable def cliff (b v:ℤ)(n:ℕ):ℤ:=2*(v-b*n)
noncomputable def banner (t:Family K):Family K:= mirror K j (gaugeT K (cliff w v n)) (chambers j w v t 1 n) * chambers j w v t 1 n
noncomputable def rungMinus (x:Family K): Family K:=
 orbitMinus j w v n x*mirror K j (r (cliff w v n)) (orbitMinus j w v n x)
noncomputable def rungPlus (x:Family K):Family K:=
 orbitPlus j w v n x*mirror K j (r (cliff w v n)) (orbitPlus j w v n x)
local notation "rM"=>rungMinus j w v n x
local notation "rP"=>rungPlus j w v n x
local notation "c₀"=>r (cliff w v n)
lemma masking (k:TestFamily K true x):S₁*(R c₀) S₁=rM*rP:=by
 let A:=orbitMinus j w v n x; let B:=orbitPlus j w v n x
 have ht: B * ((R c₀) A) = (R c₀) A * B:= even_tests K (move_ok K j _ k) (reflect_ok K j _ (move_ok K j _ (reflect_ok K j 0 k)))
 unfold sensors; rw [mirror_times]
 change A * B * ((R c₀) A * (R c₀) B)=A*((R c₀) A)*(B*((R c₀) B))
 rw [mul_assoc A B,←mul_assoc B,ht,mul_assoc,mul_assoc]
lemma centered_index:c₀=b₀*(v-w*n):=by unfold cliff; rw [two_mul,gaugeT_add,←two_mul,ruler_offset]

lemma satellite {X:Finset Cover}(x:Family K)(L R':ℤ)(q:Axis→ℤ)(d:ℕ)
   (t:InTest K true X false x)(a:Transom j X q d)(h:Between K j L R' X):
 let A:=orbitMinus j w v n x; let B:=orbitPlus j w v n x
 ∃ A' B':Finset Cover, InTest K true A' false A ∧ InTest K true B' false B ∧ Transom j A' q d ∧ Transom j B' q d∧
 Between K j (c₀-R') (c₀-L) A'∧ Between K j (c₀+2*(b₀*w*n)+L) (c₀+2*(b₀*w*n)+R') B':=by
 intro l s; let W:=reflectedBox j 0 X
 refine ⟨O _ W,O _ X,flow_port K j _ (axial K j _ t),flow_port K j _ t,?_,?_,?_,?_⟩
 · exact (a.mirro j 0).moved K j (v-w*n)
 · exact a.moved K j (v+w*n)
 · convert (h.mirror K j (0:ℤ)).relocate K j (v-w*n) using 1 <;> rw [centered_index] <;> ring
 convert h.relocate K j (v+w*n) using 1 <;> rw [centered_index] <;> ring

lemma centerpiece {X:Finset Cover}(q:Axis→ℤ)(d:ℕ)(e:0≤ w)(t:InTest K true X false f)(h:Between K j 0 (b₀*w) X)(a:Transom j X q d):
 ∃ r':Finset Cover, InTest K true r' false F₁∧ Between K j c₀ (c₀+2*(b₀*w*n)) r' ∧ Transom j r' q d:=by
 obtain ⟨s,p,q,u⟩:= mainshape K j e t h a n
 let S:=reflectedBox j 0 s
 let T:= O v (S∪s)
 refine ⟨T,flow_port K j (r v) (((axial K j _ p).mono subset_union_left).mul (p.mono subset_union_right)),?_,(trans_union j (u.mirro j 0) u).moved K j v⟩
 have hr:0< ruler K.B:=ruler_gene K.B
 have hp:=q.mirror K j (0:ℤ); simp only [mul_zero,zero_sub,neg_zero] at hp
 convert (pair_between K j hp q (by exact neg_nonpos.mpr (by positivity)) (by positivity)).relocate K j v using 1 <;> rw [centered_index] <;> ring
variable {S X:Finset Cover}(e:0 < w)(t:InTest K true S false f)(h:Between K j 0 (ruler K.B*w) S)
 (u:InTest K true X false x) (A:ℤ)(y:Between K j (2*(ruler K.B*w)) A X)
-- hypotheses selecting seam:y occupancy both ends, n=floor ...
lemma wants : True:= trivial
include p e t h u y
lemma bastion
 (l₀:2*(b₀*w*n) ≤ ((N).val:ℤ)) (l₁:((N).val:ℤ) ≤2*(b₀*w*n)+2*(b₀*w))(hr:A≤((N).val:ℤ)):
 ‖Y (chambers j w v f x n m)‖^2≤‖Y ((rM*rP) m)‖*‖Y (banner j w v n f m)‖:=by
 obtain ⟨Q,d,z,a⟩:=transversePair j S X
 obtain ⟨L',R',ha,hb,U0,V,i,k⟩:=satellite (K:=K) j w v n x _ _ Q d u a y
 obtain ⟨C,a,g,gv⟩:=centerpiece (K:=K) j w v n Q d e.le t h z
 let X':=L'∪R'
 let m':=orbitMinus j w v n x
 let p':=orbitPlus j w v n x
 have he: InTest K true X' false S₁:= (ha.mono subset_union_left).mul (hb.mono subset_union_right)
 let Q':=reflectedBox j c₀ X'
 have hx: Satin.region C N ⊆ band N j c₀ K.ℓ:= enters_arc K j (x:= c₀) (fun i t=>⟨(g i t).1,le_trans (g i t).2 (by linarith)⟩) rfl
 have ht: Satin.region Q' N⊆band N j c₀ K.ℓ:=by
    apply enters_wrapped K j
    intro i' t; obtain ⟨x,xh,xy⟩:= reflect_stays j c₀ _ t; rw [xy j,if_pos rfl]
    have hW:=ruler_gene K.B
    rcases mem_union.mp xh with v'|v'
    · obtain ⟨t,q'⟩:=i x v'; exact ⟨-x j+2*c₀,0,by push_cast; ring,by nlinarith,by linarith⟩
    obtain ⟨t,q'⟩:=k x v'; refine ⟨-x j+2*c₀+2*((N).val:ℤ),1,by push_cast; ring,?_,?_⟩
    · linarith
    nlinarith
 have hv:=seam_cut p j (2*(cliff w v n)) he a ht hx
 rw [dividing j w v n (aux_test t) (aux_test u)]
 change ‖Y ((S₁*F₁) m)‖^2 ≤‖Y ((rM*rP) m)‖ * _; rw [←masking j w v n (aux_test u)]; exact hv
-- Generate a single width covering each seam-duplicated endpoint. x can
-- move with the period PROVIDED time envelope A and other diameters fixed.
noncomputable def rim_width (A:ℤ)(d:ℕ):ℕ:= 2*A.toNat+d
local notation "μ"=>rim_width A
omit p e t h u y in
lemma rim_w (q:ℕ)(t:0≤A): 2*A≤ (μ q:ℕ):=by unfold rim_width; omega
omit p e t h u y in
lemma rim_more(q:ℕ):q≤μ q:=Nat.le_add_left ..
local notation "O₁"=>orbitMinus j w v n
local notation "O₂"=>orbitPlus j w v n
-- package support on actual torus, uniform over v and long n. include R core no X propagation required at scaled mismatch.
omit p t h
lemma rim {Q:Axis→ℤ}{d:ℕ}(z:Transom j X Q d)(a:0≤ A)(l₀:2*(b₀*w*n) ≤ ((N).val:ℤ))(l₁:((N).val:ℤ) ≤2*(b₀*w*n)+2*(b₀*w)):
 ∃ L V:Finset Cover, InTest K true L false rM ∧ InTest K true V false rP ∧
 (∀i,rest K m (Satin.region L N) i (μ d))∧(∀i,rest K m (Satin.region V N) i (μ d)):=by
 obtain ⟨L,V,ha,hb,u',v',H₁,H₂⟩:=satellite (K:=K) j w v n x _ _ Q d u z y
 let E(k:Finset Cover):=k∪reflectedBox j c₀ k
 have sale{k:Family K}{W:Finset Cover}(h: InTest K true W false k):InTest K true (E W) false (k*(R c₀) k):=(h.mono subset_union_left).mul ((axial K j c₀ h).mono subset_union_right)
 have span {X:Finset Cover}(z:Transom j X Q d)(i:Axis)(e:i≠j):rest K m (Satin.region X N) i (μ d):=by
    refine ⟨Q i,fun _ t=>?_⟩; obtain ⟨x,h,hx⟩:=mem_image.mp t; rw [←hx]
    refine ⟨x i,(z i e x h).1,le_trans (z i e x h).2 ?_,rfl⟩
    have h:=rim_more A d; omega
 refine ⟨E L,E V,sale ha,sale hb,?_,?_⟩
 · intro i; by_cases h:i=j
   · subst i; refine ⟨c₀-A,?_⟩; intro i h; obtain ⟨i,t,rfl⟩:=mem_image.mp h
     have ht:c₀-A ≤ i j ∧ i j ≤ c₀+A:=by
        have he:=ruler_gene K.B
        rcases mem_union.mp t with h|h
        · obtain ⟨a,b⟩:= H₁ i h; constructor <;> nlinarith
        obtain ⟨x,h,t⟩:=reflect_stays j c₀ L h; obtain ⟨a,b⟩:=H₁ x h
        rw [t,if_pos rfl]; constructor <;> nlinarith
     exact ⟨i j,ht.1,(by have hx:=rim_w A d a; linarith [ht.2]),rfl⟩
   exact span (trans_union j u' (u'.mirro j _)) _ h
 intro i; by_cases h:i=j
 · subst i; let θ':ℤ:=c₀+(N).val -- around opposite plane
   refine ⟨θ'-A,?_⟩; intro i h; obtain ⟨i,t,rfl⟩:=mem_image.mp h
   have he:=ruler_gene K.B; rcases mem_union.mp t with h|h
   · obtain ⟨b,q⟩:=H₂ i h; refine ⟨i j,?_,?_,rfl⟩
     · unfold θ'; linarith
     unfold θ'; linarith [rim_w A d a]
   obtain ⟨x,h,t⟩:= reflect_stays j c₀ V h; obtain ⟨b,q⟩:=H₂ x h
   refine ⟨i j+((More N).val:ℕ),?_,?_,by rw [Int.cast_add,Int.cast_natCast, ZMod.natCast_self]; simp; rfl⟩
   · rw [t,if_pos rfl,show (More N).val=(N).val*2 from rfl]; rw [Nat.cast_mul,Nat.cast_ofNat]; unfold θ'; linarith
   rw [t,if_pos rfl,show (More N).val=(N).val*2 from rfl]; rw [Nat.cast_mul,Nat.cast_ofNat]; unfold θ'; linarith [rim_w A d a]
 exact span (trans_union j v' (v'.mirro j _)) _ h
include p
omit u e y in
lemma single_hire {X:Finset Cover}(x:Family K){d:ℕ}(h:CompactArc X d)(u:InTest K true X false x)(b:ℝ)(z:pay x b)(w0:widthPair K d + addgap K ≤ (N).val):
 ‖Y (chambers j w v f x 0 m)‖ ≤ closefare K D d*(b*b):=by
 let W:= O v (reflectedBox j 0 X); let V:=O v X
 have arc {X:Finset Cover}(h:CompactArc X d): CompactArc (O v X) d:=by
    intro i
    obtain ⟨b,h⟩:=h i; refine ⟨b+(if i=j then b₀*v else 0),fun u t=> ?_⟩
    obtain ⟨x,v',rfl⟩:=plow_stays K j v X t; specialize h x v'
    rw [moves]; split_ifs <;> omega
 let a₀:=(U v) ((R 0) x); let b':=(U v) x
 have ha:InTest K true W false a₀:= flow_port K j _ (axial K j _ u)
 have ht:InTest K true V false b':= flow_port K j _ u
 rw [chambers,pin_zero,relocate_mul]
 exact all_pair p d w0 (ha.support m) (ht.support m) (torus_arc W K m (arc (h.reflBox X j _))) (torus_arc V K m (arc h)) b b (chime_pay K j _ _ (pay_flips K z j 0) m) (chime_pay K j _ _ z m)
-- rim_hire at two seams
lemma both_hire {Q:Axis→ℤ}{d:ℕ}(z:Transom j X Q d)(a:0≤ A)(l₀:2*(b₀*w*n) ≤ ((N).val:ℤ))(l₁:((N).val:ℤ) ≤2*(b₀*w*n)+2*(b₀*w))
 (hw:widthPair K (μ d)+addgap K≤ (N).val)(b:ℝ)(h:pay x b):‖Y ((rM*rP) m)‖≤ closefare K D (μ d)*(b^2*b^2):=by
 obtain ⟨U',V,g,t,hU,hV⟩:=rim (m:=m) j w v n e u A y z a l₀ l₁
 have hb:pay (orbitMinus j w v n x) b:=chime_pay K j _ _ (pay_flips K h j 0)
 have he:pay (orbitPlus j w v n x) b:= chime_pay K j _ _ h
 rw [sq]
 exact all_pair p _ hw (g.support m) (t.support m) hU hV (b*b) (b*b) (pay_mul hb (pay_flips K hb j c₀) m) (pay_mul he (pay_flips K he j c₀) m)
end seam
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.both_hire
