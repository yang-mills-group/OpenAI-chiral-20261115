import YM.CF.Vale.Basil
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
namespace Gold.Last
variable (A:S.Last D C m v)
def move(j:ℕ):= S.charge (v-1-j)+A.shift j
-- choose uniform trajectory ignoring shooting first
lemma lift_a :∃ s:ℕ→ℝ→ℝ, Arcs A s ∧∀ (i:ℕ)(x:ℝ),i < v → s i x=s (i+1) x + A.move i:=by
 let f(i:ℕ):ℝ:= ∑ w∈range (v-i),A.move (v-1-w)
 let s (i:ℕ)(x:ℝ):= x+f i
 have hs(i x)(h:i<v): s i x = s (i+1) x+A.move i:=by
    unfold s f; rw [show v-i=v-(i+1)+1 by omega,sum_range_succ,show v-1-(v-(i+1))=i by omega]; ring
 refine ⟨s, ⟨funext fun i=>?_,fun i p=> ?_,fun x i p=>?_⟩, hs⟩
 · simp [s,f]
 · unfold s; fun_prop
 dsimp only; rw [hs i _ p]; simp [move]
lemma station_room (p:A.music z)(u:2*z ≤ x)(r:room K.top.drift P.L)(w:0≤z):∃ F:ℕ→ℝ,F 0=x ∧(∀ i,i <v→ F i= F (i+1) + A.move i)∧∀ i,i≤ v→ matchedX (hat P.L x i) (F i):=by
 obtain ⟨s,hs,hX⟩:= A.lift_a; obtain ⟨i,hi,h⟩:= reach hs p u (by linarith) r w; exact ⟨fun j=> s j i,hi,fun j q=>hX j _ q,h⟩
end Gold.Last
namespace Grace
variable{V:Grace K P R}{X:Grasp V.U B e}
structure GivenX(V:Grace K P R)(X:Grasp V.U B e) where
 C:Credit
 h1:C.F=V.F1
 h2:C.f=V.f
 h3:C.U=V.F2
 h4:C.u=V.g
 z:ℝ
 hp:0<z
 n:ℕ
 flag:V.W.n ≤ n
 pearl:Pearl X
 health:0 < e
 paid: Reward X K C R P V.W
 arm{m:Side}: n ≤ m.val→∀ k, V.L.Last X C m k
 pose{m:Side}(h:n≤ m.val)(k:ℕ): (arm h k).music z
lemma blessed (p:Pearl X)(t:0<e):Nonempty (GivenX V X):=by
 obtain ⟨C,h1,h2,h3,h4,F⟩:= V.aura p t; obtain ⟨z,u,i,H⟩:= sum_cost V.up V.gate V.note V.sp p V.a_o V.b_o V.d_o t V.tallX V.L C
 let N:=i+C.i+V.W.n; let a(m: Side)(p:N≤ m.val)(v:ℕ): V.L.Last X C m v:= Classical.choice (V.L.gives F (show C.i ≤ m.val from by unfold N at p; omega) v)
 exact ⟨⟨C,h1,h2,h3,h4,z,u,N,by unfold N; omega,p,t,F,fun {m}=>a m,fun {m} p k=> H (show i ≤ m.val from by unfold N at p; omega) k (a m p k)⟩⟩
end Grace
open Grace
-- A complete unbounded schedule of stationary services (not yet an RG step identity).
structure Month (x r:ℝ)(n k j:ℕ)(V:Grace K P R){X:Grasp V.U B e}(G:GivenX V X) where
 a:ℕ→RG.BudgetPoint
 q:ℕ
 large:G.n ≤ q
 boot(i:ℕ): (a i).threshold=temp (hat P.L x i)∧(a i).B=radiusB (hat P.L x i)∧(a i).supportExponent=r ∧ (a i).power=k∧(a i).order=n
 roll(i:ℕ): Siete.Find (a i) (a (i+1)) n k (hat P.L x i) P.L
 clear{m:Side}(h:q≤ m.val)(v i:ℕ): let Y:= kint m B P.L i; Newt.Cert P K (V.L.op v Y) (V.L.mint v Y) (hat P.L x i) ∧ Seam (V.L.mint v Y) K.η K.C∧ j*(1+(a i).B) ≤ (cell m B P.L i).val
 pitch{m:Side}(h:q≤ m.val)(v:ℕ):∀ F, Arcs (G.arm (large.trans h) v) F → ∃ b:ℝ,F 0 b=x∧∀ i,i≤ v → matchedX (hat P.L x i) (F i b)
 book{m:Side}(h:q≤ m.val) (v:ℕ): ∃ F:ℕ→ℝ,F 0=x∧(∀ i,i<v →F i=F (i+1)+(G.arm (large.trans h) v).move i)∧∀ i,i ≤ v→matchedX (hat P.L x i) (F i)
lemma Month.existsX(n k j:ℕ)(hp:6 ≤ n)(ht:2 ≤ k)(V:Grace K P R){X:Grasp V.U B e}(G:GivenX V X): ∀ᶠ x in atTop,∀ r:ℝ,0<r→ Nonempty (Month x r n k j V G):=by
 filter_upwards [fates n k hp ht P.L,mastK P.L,eventually_ge_atTop (2*G.z)] with x ha hz hx r hr
 obtain ⟨A,H,Y⟩:=ha r hr
 let u:=1+radiusB (hat P.L x 0); let q:= G.n+ (100+j)*u; have hh: G.n≤ q:=by unfold q; omega
 refine ⟨⟨A,q,hh,fun i=>?_,Y,fun {m} v i t=>?_, fun {m} v i F P=>reach P (G.pose _ i) hx (by linarith [G.hp]) V.roomZ G.hp.le,fun {m} v i=> Gold.Last.station_room (G.arm ..) (G.pose (hh.trans v) i) hx V.roomZ G.hp.le⟩⟩
 · grind
 let h':=(100+j); have he:(100+j)* (1+radiusB (hat P.L x t)) ≤ (cell m B P.L t).val:= bulk_size x h' t (by have h:=V.tallX; omega) hz ((by unfold q h'; omega : h'*u≤q).trans v)
 have hX: G.n ≤ (cell m B P.L t).val:= hh.trans (v.trans (amplit ..)); let E:= kint m B P.L t
 refine ⟨V.L.cert i E ?_ _ ?_, V.L.seamL ..,?_⟩
 · change V.W.n ≤ (cell m B P.L t).val*2; have hv:= G.flag; omega
 · refine ((Nat.mul_le_mul_right _ (Nat.le_add_right 100 j)).trans he).trans ?_; change (cell m B P.L t).val ≤ (cell m B P.L t).val*2; omega
 rw [(H t).2.2.2.1]; exact (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)).trans he
-- one-shot unconditional fixed environments with adjustable sizes. Expose clean end clock for later assembly.
lemma score(j n k:ℕ)(p:4 ≤ j)(h:Even j)(hp:6 ≤ n)(ht:2 ≤ k):∃ (K:Teller group) (Z:ChartRatio group), LocalRatio Z∧1 ≤ K.C∧K.j=j∧K.top.clip.direct ≤ 1∧(∀ P:RG.Patch, P.Branches K.bind group)∧ ∃ N:ℕ,∀ (P:RG.Patch),N ≤ P.L.val →P.J=j → ∃ (V:Grace K P Z)(T:Acorn.Repair K.j)(i:ℕ),∀ B:ℕ,i ≤ B→∃ e:ℝ,0<e ∧∀ y:ℝ,0<y → y≤ e →∃ (X:Grasp V.U (P.L^B) y)(G:GivenX V X), y ≤ T.d∧ X.baseline ≤ T.d∧ T.n ≤ X.roundZ ∧∀ u:ℕ,∀ᶠ b:ℝ in atTop,∀ r:ℝ,0<r→Nonempty (Month b r n k u V G):=by
 obtain ⟨Z,Y⟩:= LocalH.actual group; obtain ⟨K,hK,z,u,w,N,H⟩:= sun j p h Z Y
 refine ⟨K,Z,Y,z,hK,u,w,N,fun P x t=>?_⟩; obtain ⟨F⟩:=H P x t; obtain ⟨D⟩:=Acorn.restoreX K.j (by omega); obtain ⟨i,h',v⟩:=spices F D 1
 refine ⟨F,D,i,fun B p=>?_⟩; obtain ⟨e,g,f⟩:=v B p; refine ⟨e,g,fun y z q=>?_⟩; obtain ⟨D',⟨P⟩,a,b,c⟩:= f y z q; obtain ⟨R⟩:=blessed P z
 exact ⟨D',R,a,b,c,fun i=> Month.existsX n k i hp ht F R⟩
end YM.CF.Vale
