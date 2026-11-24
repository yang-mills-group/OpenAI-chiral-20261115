import YM.SU5.FiniteGaugeData.Hierarchy.Unit
/-! # BOTH operator norm compactness in the one-step transfer of actual wide Families,
and collective compactness of the images of arbitrary bounded input sets. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
section
variable {I J V W:Type*}
-- metric ε-conclusion from any determining approximation estimate on finite pieces
lemma equip [PseudoMetricSpace W] {t:ℝ}(p:0<t)(A:I→W)(h:TotallyBounded (Set.range A)): ∃ Z:Set I,Z.Finite ∧ ∀ x, ∃ y∈ Z, dist (A x) (A y) < t:=by
  classical
  obtain ⟨X,v,P,g⟩:= Metric.finite_approx_of_totallyBounded h t p; choose f e using fun x:↥X=> v x.property
  haveI : Fintype X := P.fintype
  refine ⟨Set.range f,Set.finite_range f,fun x=>?_⟩
  have hx:= g (show A x∈ Set.range A from ⟨x,rfl⟩); simp only [Set.mem_iUnion] at hx; obtain ⟨y,z,t⟩:=hx
  exact ⟨f ⟨y,z⟩,⟨_,rfl⟩,by rw [e]; exact t⟩
lemma issue [PseudoMetricSpace W] {t:ℝ}(A:I→W){Z:Set I}(h:Z.Finite)(p:∀ x, ∃ y∈ Z,dist (A x) (A y)< t) : ∃ T:Set W,T.Finite ∧ Set.range A ⊆ ⋃ y∈T, ball y t:=by
  refine ⟨A '' Z,h.image _,?_⟩; rintro v ⟨x,rfl⟩; obtain ⟨y,h,t⟩:= p x; exact Set.mem_iUnion.mpr ⟨A y,Set.mem_iUnion.mpr ⟨⟨y,h,rfl⟩,t⟩⟩
lemma coordinate_full {V:J→Type*}[∀j,MetricSpace (V j)][∀j,CompleteSpace (V j)](A:I→∀j,V j)
    (h:∀ j, TotallyBounded (Set.range fun i=> A i j)) : TotallyBounded (Set.range A):=by
  let K(j:J):= closure (Set.range fun i=> A i j); have hp(j:J):IsCompact (K j):=(h j).closure.isCompact_of_isClosed isClosed_closure
  exact (isCompact_univ_pi hp).totallyBounded.subset (by rintro v ⟨i,rfl⟩; intro j _; exact subset_closure ⟨i,rfl⟩)

variable (S:Finset Cover)
lemma panel_tB (f:I→BC S)(h: Menu (fun i v=> slit (f i).val v)): TotallyBounded (Set.range f):=by
  classical
  obtain ⟨C,c,v⟩:=h.budget
  refine Metric.totallyBounded_iff.mpr fun ε e=> ?_
  obtain ⟨P,x,p⟩:=h.deal (ε/4) (by linarith); let y : P.Sign→PairsC:= fun s=>if h:∃ x,P.idT x=s then Classical.choose h else (1,1)
  have hy(x):P.withZ (y (P.idT x)) x := by
    have he:∃ y,P.idT y=P.idT x:=⟨x,rfl⟩; unfold y; rw [dif_pos he]; exact Deck.id_spec _ _ _ (Classical.choose_spec he)
  let N(i:I)(a:P.Sign):= slit (f i).val (y a)
  obtain ⟨Z,f',h⟩:= equip (t:=ε/4) (by linarith) N (coordinate_full N fun a=> (isCompact_closedBall (0:ℂ) C).totallyBounded.subset (by rintro x ⟨i,rfl⟩; exact mem_closedBall_zero_iff.mpr (v i (y a))))
  apply issue _ f'; intro i; obtain ⟨j,x,H⟩:=h i; refine ⟨j,x,?_⟩; rw [dist_eq_norm]; apply lt_of_le_of_lt ((stock_n_iff S (by linarith:0≤3*(ε/4)) _).mpr ?_) (by linarith)
  intro x'; change ‖slit (f i).val x' - slit (f j).val x'‖ ≤ _; rw [← dist_eq_norm]
  let u:=P.idT x'; have h(x:I): dist (slit (f x).val x') (N x u)< ε/4:=by rw [dist_comm]; exact p _ _ (hy x') x
  have r: dist (N i u) (N j u) ≤ ε/4:= (dist_le_pi_dist ..).trans H.le
  exact (dist_triangle4_right _ _ (N i u) (N j u)).trans (by linarith [h i,h j])
end
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "I₀"=> PaidPt Y S s
local notation "W₀"=> GridStep Λ l S
local notation "P"=> transitionQ Y h S s
local notation "V"=> Catalog W₀

lemma collective {I:Type*}(p:I→ PaidPt Y S s)(A:I→ Catalog S)(w:ℝ)(u:∀i,‖A i‖≤w):
    IsCompact (closure (Set.range fun i=> transitionQ Y h S s (p i) (A i))) := by
  apply (TotallyBounded.closure _).isCompact_of_isClosed isClosed_closure
  exact coordinate_full (fun i:I=> ((P) (p i) (A i) : Key W₀→BC W₀)) fun a => panel_tB W₀ _ (everyKey Y h S s p A w u (fun _=>a))

lemma price_compass : TotallyBounded (Set.range (transitionQ Y h S s)) := by
  classical
  refine (Metric.totallyBounded_iff («α»:=Catalog S →L[ℂ] Catalog W₀)).mpr fun ε e=>?_
  obtain ⟨K,t⟩:= patrons_Q Y h S s (ε/4) (by linarith)
  let v(i:I₀)(a:K):Catalog W₀:= (P) i a.val.val
  obtain ⟨Z,c,f⟩:= Hierarchy.equip (t:=ε/4) (by linarith) v (coordinate_full v fun i:K=> ((collective Y h S s (fun j:I₀=> j) (fun _=> i.val.val) 1 (fun _=>i.val.property)).totallyBounded.subset subset_closure))
  apply issue _ c; intro i; obtain ⟨j,u,f⟩:= f i; refine ⟨j,u,?_ ⟩; rw [dist_eq_norm ((P) i) ((P) j)]
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm (show 0≤3* (ε/4) by linarith) ?_) (by linarith)
  intro x p; let d:Orb S:= ⟨x,p.le⟩; obtain ⟨k,hk,v'⟩:=t d
  let a:K:=⟨k,hk⟩
  change ‖(P) i x - (P) j x‖ ≤ _; rw [← dist_eq_norm]; have he:=v' i; have hh:=v' j; change dist ((P) i x) (v i a) ≤ _ at he; change dist ((P) j x) (v j a) ≤ _ at hh; have hr:dist (v i a) (v j a)< ε/4:= lt_of_le_of_lt (dist_le_pi_dist ..) f; exact (dist_triangle4_right _ _ (v i a) (v j a)).trans (by linarith only [he,hh,hr])

lemma compactum : IsCompact (closure (Set.range (transitionQ Y h S s))) :=
  (price_compass Y h S s).closure.isCompact_of_isClosed isClosed_closure
#print axioms compactum
end YM.CF.Buffered.Afterglow.Hierarchy
