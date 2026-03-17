import tkinter as tk
from tkinter import ttk, messagebox
import os
from datetime import datetime
import re
import webbrowser  # 링크 열기 위한 모듈

# 파일 경로 설정
SAVE_FILE = "all_notes.txt"
CONTACTS_FILE = "Contacts.txt"
NOTES_PER_PAGE = 25  # 한 페이지당 노트 수

# 템플릿 파일 경로
TEMPLATE_IRD = "Template_IRD.txt"
TEMPLATE_IRD2 = "Template_IRD2.txt"
TEMPLATE_CLOSURE = "Template_Closure.txt"
TEMPLATE_THNXS = "Template_Thnxs.txt"

# 진행상태 옵션
STATUS_OPTIONS = ["Working", "Waiting for cu", "TODO", "TBD", "Done", "SPR Filed", "Cancel", "Monitoring", "Always", "Deleted", "Joe"]

class NoteApp:
    def __init__(self, root):
        self.root = root
        self.root.title("노트 앱 - 케이스 관리 + 연락처 관리")
        self.root.geometry("1100x800")

        # ===== 인스턴스 변수로 list_hscroll 선언 =====
        self.list_hscroll = None  # 수평 스크롤바 인스턴스 변수
        self.list_vscroll = None  # 수직 스크롤바 인스턴스 변수
        # ==================================================
    
        # ===== 재귀 호출 방지 플래그 =====
        self.is_saving = False          # save_to_txt 재귀 방지
        self.is_applying_filters = False # apply_all_filters 재귀 방지
        self.is_saving_changes = False  # save_only_if_changed 재귀 방지
        # =====================================
        
        # 리스트박스 선택 스타일 설정
        self.root.option_add('*Listbox.selectBackground', '#347083')
        self.root.option_add('*Listbox.selectForeground', 'black')

        # ==== 하이라이트 유지용 ====
        self.selected_note_id = None  # 선택된 노트 ID
        self.selected_list_index = -1 # 선택된 리스트 인덱스
        # ========================================

        # ==== 검색 기능 변수 ====
        self.search_var = tk.StringVar()
        self.case_sensitive_var = tk.BooleanVar(value=False)  # 대소문자 구분 기본값 OFF
        # 실시간 검색을 위한 타이머 변수
        self.search_timer = None

        # 기본 변수
        self.notes = []
        self.contacts = []  # 연락처 데이터
        self.current_id = None
        self.sort_by = "name"
        self.sort_order = "asc"
        self.current_page = 1
        self.total_pages = 1
        self.wrap_mode = tk.WORD
        self.wrap_text = "줄바꿈 OFF"
        self.original_title = ""
        self.original_content = ""
        
        # 현재 선택된 연락처 ID / 신규 요청자 플래그
        self.current_contact_id = None
        self.is_new_contact = False  # 신규 요청자 선택 여부
        
        # 상태 필터 변수
        self.status_filter_vars = {}
        self.filtered_notes = []

        # ==== 앱 종료 시 자동 저장 ====
        self.root.protocol("WM_DELETE_WINDOW", self.on_app_close)
        # ====================================
        
        # ===== Catalog 트리 관련 변수 =====
        self.markdown_headers = []  # Markdown 헤더 정보 저장 (텍스트, 시작위치, 레벨)
        self.catalog_tree = None    # Catalog 트리 위젯
        self.catalog_frame = None   # Catalog 프레임
        # ==================================
    
        # UI 생성 및 데이터 로드 (생성 순서)
        self.create_ui()
        self.load_contacts()  # 연락처 먼저 로드
        self.load_from_txt()
        self.apply_status_filter()  # 페이지 요소 생성 후 필터 적용
        self.calculate_pages()
        self.refresh_list()
        
        # Catalog 트리 초기화 (UI 생성 후 호출)
        self.root.after(100, self.update_catalog_tree)
        
        # 템플릿 파일 초기화
        self.init_template_files()
        
        # 리스트박스 선택 색상 초기화
        self.listbox.configure(selectbackground='#347083', selectforeground='black')
        
        self.listbox.configure(xscrollcommand=lambda *args: self.list_hscroll.set(*args))
        # 수평 스크롤바를 항상 표시
        #self.list_hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.list_hscroll.config(command=self.listbox.xview)
        # 리스트박스의 수평 스크롤 위치를 항상 왼쪽으로 초기화
        self.listbox.xview_moveto(0)
        
        # 내용 텍스트 위젯의 선택 색상 설정
        self.content_txt.configure(
            selectbackground='#347083',  # 선택 배경색
            selectforeground='black',    # 선택 글자색
            selectborderwidth=0
        )        
        
        # ==== 하이라이트 기능 변수 ====
        self.highlight_timer = None  # 하이라이트 디바운싱 타이머
        self.is_highlight_processing = False  # 하이라이트 처리 중 여부
        self.last_selected_text = ""  # 마지막 선택 텍스트 저장
        
        # SQL 태그 스타일 설정 (연한 빨간색으로 변경)
        self.content_txt.tag_configure("sql_string", foreground="#ff6666")  # 연한 빨강
        self.content_txt.tag_configure("sql_keyword", foreground="#0066cc")  # 연한 파랑
        self.content_txt.tag_configure("sql_comment", foreground="#669933")  # 연한 초록
        self.content_txt.tag_configure("sql_identifier", foreground="#996633")  # 연한 갈색
        
        # ===== CMD 블록 강조 초기화 =====
        self.schedule_cmd_highlight()
        
        # ===== XML 블록 강조 초기화 =====
        self.schedule_xml_highlight()

        # ===== Markdown 제목 강조 초기화 (편집기 오픈 시 한 번만 실행) =====
        self.highlight_markdown_headers()  # 실시간 예약 제거, 직접 실행

    # ==== 앱 종료 메서드 ====
    def on_app_close(self):
        """앱 종료 시 변경사항 자동 저장 후 종료"""
        self.save_only_if_changed()  # 변경사항 저장
        
        # 新增：清理所有定时器
        for timer_attr in ['search_timer', 'link_update_timer', 'sql_update_timer', 
                           'record_update_timer', 'cmd_update_timer', 'xml_update_timer',
                           'markdown_update_timer', 'highlight_timer', '_title_height_timer',
                           '_comment_height_timer']:
            if hasattr(self, timer_attr) and getattr(self, timer_attr):
                self.root.after_cancel(getattr(self, timer_attr))
        
        self.root.destroy()  # 앱 종료

    # ================== UI 인터페이스 생성 ==================
    def create_ui(self):
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # 왼쪽 프레임 (정렬 → 상태 필터 → 리스트 → 페이징 → 액션 버튼 → 상태정보)
        left_frame = ttk.Frame(main_paned)
        main_paned.add(left_frame, weight=2)

        # 1. 정렬 옵션 프레임
        sort_frame = ttk.LabelFrame(left_frame, text="정렬")
        sort_frame.pack(fill=tk.X, pady=2)

        self.sort_buttons = {}
        sort_options = [("이름순", "name"), ("수정순", "update"), ("생성순", "create")]
        for idx, (text, value) in enumerate(sort_options):
            btn = ttk.Button(sort_frame, text=f"{text} (내림차순)", 
                           command=lambda v=value: self.toggle_sort(v))
            btn.grid(row=0, column=idx, padx=2, pady=2, sticky="ew")
            self.sort_buttons[value] = btn

        # 2. 상태 필터 프레임 (Multiple Selection Filter) - 두 줄로 반반 배치 + 버튼 왼쪽 정렬
        filter_frame = ttk.LabelFrame(left_frame, text="진행상태 필터")
        filter_frame.pack(fill=tk.X, pady=2)

        # ===== Select All / Reset 버튼 (왼쪽 정렬) =====
        filter_btn_frame = ttk.Frame(filter_frame)
        filter_btn_frame.pack(fill=tk.X, pady=1, anchor="w")

        select_all_btn = ttk.Button(filter_btn_frame, text="Select All", 
                                  command=self.select_all_status, width=8)
        select_all_btn.pack(side=tk.LEFT, padx=1)
        reset_btn = ttk.Button(filter_btn_frame, text="Reset", 
                             command=self.reset_status_filter, width=6)
        reset_btn.pack(side=tk.LEFT, padx=1)

        # ===== 체크박스 두 줄로 반반 배치 =====
        checkbox_container = ttk.Frame(filter_frame)
        checkbox_container.pack(fill=tk.X, pady=1)

        # 상태 목록을 두 부분으로 나누기 (반반)
        status_count = len(STATUS_OPTIONS)
        half_idx = (status_count + 1) // 2  # 홀수일 경우 앞쪽에 하나 더 배치
        first_half = STATUS_OPTIONS[:half_idx]
        second_half = STATUS_OPTIONS[half_idx:]

        # 첫 번째 줄 프레임
        checkbox_row1 = ttk.Frame(checkbox_container)
        checkbox_row1.pack(fill=tk.X, pady=1)

        # 두 번째 줄 프레임
        checkbox_row2 = ttk.Frame(checkbox_container)
        checkbox_row2.pack(fill=tk.X, pady=1)

        # 첫 번째 줄에 반반 배치
        for status in first_half:
            var = tk.BooleanVar()
            default_value = status in ["Working", "Waiting for cu"]
            var.set(default_value)
            self.status_filter_vars[status] = var
            
            chk = ttk.Checkbutton(checkbox_row1, text=status, variable=var, 
                                command=self.apply_status_filter)
            chk.pack(side=tk.LEFT, padx=2, pady=0)

        # 두 번째 줄에 나머지 반반 배치
        for status in second_half:
            var = tk.BooleanVar()
            default_value = status in ["Working", "Waiting for cu"]
            var.set(default_value)
            self.status_filter_vars[status] = var
            
            chk = ttk.Checkbutton(checkbox_row2, text=status, variable=var, 
                                command=self.apply_status_filter)
            chk.pack(side=tk.LEFT, padx=2, pady=0)
            
        # 2.5 검색 프레임
        search_frame = ttk.LabelFrame(left_frame, text="검색")
        search_frame.pack(fill=tk.X, pady=2)

        # 검색 입력창 + 체크박스 프레임 (가로 정렬)
        search_inner_frame = ttk.Frame(search_frame)
        search_inner_frame.pack(fill=tk.X, padx=5, pady=3)

        self.search_entry = ttk.Entry(search_inner_frame, textvariable=self.search_var, font=("맑은 고딕", 10))
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))

        # 대소문자 구분 체크박스 (클릭 시 즉시 필터 적용)
        case_check = ttk.Checkbutton(
            search_inner_frame,
            text="CS",  # Case Sensitive 약자로 작게 표시
            variable=self.case_sensitive_var,
            # 클릭 시 즉시 검색 필터 적용 (타이머 없이 바로 실행)
            command=lambda: self.apply_all_filters(reset_page=True)
        )
        case_check.pack(side=tk.RIGHT)

        # 스타일 설정 (체크박스 더 작게)
        style = ttk.Style()
        style.configure("Small.TCheckbutton", font=("맑은 고딕", 8))
        
        # 실시간 검색 이벤트 바인딩
        self.search_var.trace('w', self.on_search_change)  # 텍스트 변경 시 실행
        self.search_entry.bind('<FocusOut>', self.on_search_change)  # 포커스 잃을 때
        self.search_entry.bind('<Return>', lambda e: None)  # 엔터 누를 때 중복 실행 방지

        # 3. 메모 리스트 (스크롤바 포함)
        list_container = ttk.Frame(left_frame)
        # anchor="w" 로 왼쪽 정렬
        list_container.pack(fill=tk.BOTH, expand=True, pady=(0, 5), anchor="w")

        self.list_vscroll = ttk.Scrollbar(list_container, orient=tk.VERTICAL)
        self.list_hscroll = ttk.Scrollbar(list_container, orient=tk.HORIZONTAL)

        self.listbox = tk.Listbox(
            list_container, 
            font=("맑은 고딕", 11),
            yscrollcommand=self.list_vscroll.set,
            xscrollcommand=self.list_hscroll.set,
            width=50,  # 명시적으로 width 지정 (주석 해제 + 값 설정)
            height=15
        )
        
        self.list_vscroll.config(command=self.listbox.yview)
        self.list_hscroll.config(command=self.listbox.xview)
        
        self.listbox.grid(row=0, column=0, sticky="nsew")
        self.list_vscroll.grid(row=0, column=1, sticky="ns")
        self.list_hscroll.grid(row=1, column=0, sticky="ew")

        # 수평 스크롤바를 항상 표시하도록 설정
        self.list_hscroll.grid_remove()  # 일단 숨기고
        self.list_hscroll.grid()         # 다시 표시
        # 리스트박스의 수평 스크롤 위치 초기화
        self.listbox.xview_moveto(0)
        # ===============================
        
        list_container.grid_rowconfigure(0, weight=1)
        list_container.grid_columnconfigure(0, weight=1)
        
        self.listbox.bind("<<ListboxSelect>>", self.switch_note)

        # 4. 페이징 프레임
        page_frame = ttk.Frame(left_frame)
        page_frame.pack(fill=tk.X, pady=2)
        
        self.prev_btn = ttk.Button(page_frame, text="◀ 이전", command=self.prev_page)
        self.prev_btn.pack(side=tk.LEFT, padx=2)
        
        self.page_label = ttk.Label(page_frame, text=f"페이지 1 / 1")
        self.page_label.pack(side=tk.LEFT, padx=5)
        
        self.next_btn = ttk.Button(page_frame, text="다음 ▶", command=self.next_page)
        self.next_btn.pack(side=tk.LEFT, padx=2)

        # 5. 기능 버튼 프레임 (삭제 버튼 제거, 새 노트 버튼만 유지)
        btn_frame = ttk.Frame(left_frame)
        btn_frame.pack(fill=tk.X, pady=2)

        btn_container = ttk.Frame(btn_frame)
        btn_container.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # 새 노트 버튼 (남은 넓이 모두 차지)
        self.new_btn = ttk.Button(btn_container, text="새 노트", command=self.create_new_note)
        self.new_btn.pack(side=tk.LEFT, padx=2, fill=tk.X, expand=True)

        # Deleted 노트의 영구삭제 버튼 (글자만큼 넓이 차지)
        self.delete_perm_btn = ttk.Button(
            btn_container,
            text="Deleted 노트의 영구삭제",
            command=self.permanently_delete_status_deleted,
            width=len("Deleted 노트의 영구삭제") + 2  # 글자 길이만큼 넓이 지정
        )
        self.delete_perm_btn.pack(side=tk.LEFT, padx=2)

        # 6. 상태정보 영역
        status_frame = ttk.LabelFrame(left_frame, text="상태 정보")
        status_frame.pack(fill=tk.X, padx=5, pady=3)
        self.status_label = ttk.Label(status_frame, text="총 노트 수: 0 | 필터된 노트 수: 0 | 정렬: 수정순 (내림차순)")
        self.status_label.pack(padx=5, pady=2)

        # 중간 영역과 Catalog 영역을 위한 PanedWindow 생성
        middle_catalog_paned = ttk.PanedWindow(main_paned, orient=tk.HORIZONTAL)
        main_paned.add(middle_catalog_paned, weight=3)  # weight=4 → weight=3으로 변경

        # 오른쪽 프레임 (편집 영역 - 기존 유지)
        content_container = ttk.Frame(middle_catalog_paned)
        middle_catalog_paned.add(content_container, weight=3)

        # ID/생성시간/수정시간 영역
        info_frame = ttk.LabelFrame(content_container, text="노트 정보")
        info_frame.pack(fill=tk.X, pady=(0, 5))
        
        ttk.Label(info_frame, text="ID:", font=("맑은 고딕", 9)).grid(row=0, column=0, sticky="w", padx=5)
        self.id_ent = ttk.Entry(info_frame, state="readonly", width=8, font=("맑은 고딕", 9))
        self.id_ent.grid(row=0, column=1, sticky="w")

        ttk.Label(info_frame, text="생성 시간:", font=("맑은 고딕", 9)).grid(row=0, column=2, sticky="w", padx=10)
        self.create_ent = ttk.Entry(info_frame, state="readonly", width=20, font=("맑은 고딕", 9))
        self.create_ent.grid(row=0, column=3, sticky="w")

        ttk.Label(info_frame, text="수정 시간:", font=("맑은 고딕", 9)).grid(row=0, column=4, sticky="w", padx=10)
        self.update_ent = ttk.Entry(info_frame, state="readonly", width=20, font=("맑은 고딕", 9))
        self.update_ent.grid(row=0, column=5, sticky="w")

        # ================== 케이스 정보 영역 ==================
        case_frame = ttk.LabelFrame(content_container, text="케이스 정보")
        case_frame.pack(fill=tk.X, pady=(0, 5))
        
        # 케이스 번호
        ttk.Label(case_frame, text="케이스 번호:", font=("맑은 고딕", 9)).grid(row=0, column=0, sticky="w", padx=5)
        self.case_number_ent = ttk.Entry(case_frame, width=12, font=("맑은 고딕", 9))
        self.case_number_ent.grid(row=0, column=1, sticky="w", padx=5)
        
        # Ref. Case
        ttk.Label(case_frame, text="Ref. Case:", font=("맑은 고딕", 9)).grid(row=0, column=2, sticky="w", padx=10)
        self.ref_case_ent = ttk.Entry(case_frame, width=12, font=("맑은 고딕", 9))
        self.ref_case_ent.grid(row=0, column=3, sticky="w", padx=5)
        
        # 진행상태 (새로운 옵션 포함)
        ttk.Label(case_frame, text="진행상태:", font=("맑은 고딕", 9)).grid(row=0, column=4, sticky="w", padx=10)
        self.status_combobox = ttk.Combobox(case_frame, values=STATUS_OPTIONS, width=15, font=("맑은 고딕", 9), state="readonly")
        self.status_combobox.grid(row=0, column=5, sticky="w", padx=5)

        # ================== 요청자 정보 영역 ==================
        requester_frame = ttk.LabelFrame(content_container, text="요청자 정보")
        requester_frame.pack(fill=tk.X, pady=(0, 5))
        
        # 요청자 선택 콤보박스 (기본값 --)
        ttk.Label(requester_frame, text="요청자 선택:", font=("맑은 고딕", 9)).grid(row=0, column=0, sticky="w", padx=5)
        self.requester_combobox = ttk.Combobox(requester_frame, width=30, font=("맑은 고딕", 9), state="readonly")
        self.requester_combobox.grid(row=0, column=1, columnspan=6, sticky="we", padx=5)
        self.requester_combobox.bind("<<ComboboxSelected>>", self.load_requester_info)
        
        # 요청자 상세 정보 (2번째 행 - 한 줄에 배치)
        # Name
        ttk.Label(requester_frame, text="이름:", font=("맑은 고딕", 9)).grid(row=1, column=0, sticky="w", padx=5)
        self.requester_name_ent = ttk.Entry(requester_frame, width=12, font=("맑은 고딕", 9))
        self.requester_name_ent.grid(row=1, column=1, sticky="w", padx=5)
        
        # Role
        ttk.Label(requester_frame, text="직함:", font=("맑은 고딕", 9)).grid(row=1, column=2, sticky="w", padx=5)
        self.requester_role_ent = ttk.Entry(requester_frame, width=12, font=("맑은 고딕", 9))
        self.requester_role_ent.grid(row=1, column=3, sticky="w", padx=5)
        
        # Email
        ttk.Label(requester_frame, text="이메일:", font=("맑은 고딕", 9)).grid(row=1, column=4, sticky="w", padx=5)
        self.requester_email_ent = ttk.Entry(requester_frame, width=18, font=("맑은 고딕", 9))
        self.requester_email_ent.grid(row=1, column=5, sticky="w", padx=5)
        
        # Phone
        ttk.Label(requester_frame, text="전화번호:", font=("맑은 고딕", 9)).grid(row=1, column=6, sticky="w", padx=5)
        self.requester_phone_ent = ttk.Entry(requester_frame, width=20, font=("맑은 고딕", 9))
        self.requester_phone_ent.grid(row=1, column=7, sticky="w", padx=5)
        
        # Survey Count
        ttk.Label(requester_frame, text="Survey Count:", font=("맑은 고딕", 9)).grid(row=1, column=8, sticky="w", padx=5)
        self.survey_count_ent = ttk.Entry(requester_frame, width=5, font=("맑은 고딕", 9))
        self.survey_count_ent.grid(row=1, column=9, sticky="w", padx=5)
        
        # 비고란
        ttk.Label(requester_frame, text="비고:", font=("맑은 고딕", 9)).grid(row=2, column=0, sticky="nw", padx=5, pady=5)
        self.requester_comment_text = tk.Text(
            requester_frame,
            font=("맑은 고딕", 9),
            height=2,
            wrap=tk.WORD,
            undo=True
        )
        self.requester_comment_text.grid(row=2, column=1, columnspan=9, sticky="we", padx=5, pady=5)
        # 비고 영역 높이 조절 이벤트 바인딩
        self.requester_comment_text.bind("<KeyPress>", self.adjust_comment_height)
        self.requester_comment_text.bind("<KeyRelease>", self.adjust_comment_height)
        self.requester_comment_text.bind("<Control-v>", self.adjust_comment_height)
        self.requester_comment_text.bind("<MouseWheel>", self.adjust_comment_height)
        self.requester_comment_text.bind("<ButtonRelease>", self.adjust_comment_height)
        self.requester_comment_text.bind("<Configure>", self.adjust_comment_height)
        self.requester_comment_text.bind("<Control-z>", self.undo_comment)
        self.requester_comment_text.bind("<Control-y>", self.redo_comment)
        self.requester_comment_text.bind("<Control-Z>", self.undo_comment)
        self.requester_comment_text.bind("<Control-Y>", self.redo_comment)

        # ================== 제목 영역 ==================
        ttk.Label(content_container, text="제목", font=("맑은 고딕", 10)).pack(anchor=tk.W)
        self.title_text = tk.Text(
            content_container,
            font=("맑은 고딕", 12),
            height=3,
            wrap=tk.WORD,
            undo=True,
        )
        self.title_text.pack(fill=tk.X, pady=3)
        
        # 제목 이벤트 바인딩
        self.title_text.bind("<KeyPress>", self.adjust_title_height)
        self.title_text.bind("<KeyRelease>", self.adjust_title_height)
        self.title_text.bind("<Control-v>", self.adjust_title_height)
        self.title_text.bind("<MouseWheel>", self.adjust_title_height)
        self.title_text.bind("<ButtonRelease>", self.adjust_title_height)
        self.title_text.bind("<Configure>", self.adjust_title_height)
        self.title_text.bind("<Control-z>", self.undo_title)
        self.title_text.bind("<Control-y>", self.redo_title)
        self.title_text.bind("<Control-Z>", self.undo_title)
        self.title_text.bind("<Control-Y>", self.redo_title)

        # ================== 템플릿 + 줄바꿈 버튼 통합 프레임 (한 줄로 배치) ==================
        template_wrap_frame = ttk.Frame(content_container)
        template_wrap_frame.pack(fill=tk.X, pady=2)

        # 템플릿 버튼 (왼쪽 배치)
        self.ird_btn = ttk.Button(template_wrap_frame, text="IRD 템플릿", command=lambda: self.insert_template("IRD"))
        self.ird_btn.pack(side=tk.LEFT, padx=2)

        self.closure_btn = ttk.Button(template_wrap_frame, text="IRD with Ref. 템플릿", command=lambda: self.insert_template("IRD2"))
        self.closure_btn.pack(side=tk.LEFT, padx=2)

        self.thnxs_btn = ttk.Button(template_wrap_frame, text="Common 템플릿", command=lambda: self.insert_template("Thnxs"))
        self.thnxs_btn.pack(side=tk.LEFT, padx=2)

        self.thnxs_btn = ttk.Button(template_wrap_frame, text="Closure 템플릿", command=lambda: self.insert_template("Closure"))
        self.thnxs_btn.pack(side=tk.LEFT, padx=2)

        # 빈 공간 채우기 (템플릿 버튼과 줄바꿈 버튼 사이 공간 확보)
        ttk.Label(template_wrap_frame).pack(side=tk.LEFT, expand=True)

        # 줄바꿈 버튼 (오른쪽 배치)
        self.wrap_btn = ttk.Button(template_wrap_frame, text=self.wrap_text, command=self.toggle_wrap)
        self.wrap_btn.pack(side=tk.RIGHT, padx=2)

        # ================== 내용 영역 제어 프레임 ==================
        ttk.Label(content_container, text="내용", font=("맑은 고딕", 10)).pack(anchor=tk.W)

        # 내용 입력 영역
        content_frame = ttk.Frame(content_container)
        content_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        content_vscroll = ttk.Scrollbar(content_frame, orient=tk.VERTICAL)
        content_hscroll = ttk.Scrollbar(content_frame, orient=tk.HORIZONTAL)
        
        content_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        content_hscroll.pack(side=tk.BOTTOM, fill=tk.X)

        self.content_txt = tk.Text(
            content_frame,
            font=("맑은 고딕", 11),
            wrap=self.wrap_mode,
            yscrollcommand=content_vscroll.set,
            xscrollcommand=content_hscroll.set,
            undo=True,
            # 탭 너비 설정 + 공백 유지
            tabs=("2c",),  # 탭을 2문자 너비로 설정 (원하는 값으로 조절 가능)
            insertwidth=1,
            selectborderwidth=0
        )
        self.content_txt.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        content_vscroll.config(command=self.content_txt.yview)
        content_hscroll.config(command=self.content_txt.xview)
        
        self.content_txt.bind("<Control-z>", self.undo_content)
        self.content_txt.bind("<Control-y>", self.redo_content)
        self.content_txt.bind("<Control-Z>", self.undo_content)
        self.content_txt.bind("<Control-Y>", self.redo_content)
        
        # ===== 하이라이트 기능 =====
        # 하이라이트 태그 정의 (노란색 배경 + 강화된 설정)
        self.content_txt.tag_configure(
            "highlight", 
            background="yellow",
            relief="flat",  # 테두리 없애기
            borderwidth=0   # 테두리 너비 0
        )
        # ===============================

        # ===== 링크 기능 =====
        # 링크 태그 정의 (파란색 + 밑줄)
        self.content_txt.tag_configure(
            "link",
            foreground="blue",
            underline=True
        )
        # ===========================

        # ===== 태그 우선순위 설정 (모든 태그 정의 후에 한번에 설정) =====
        # 1. 선택 태그(sel) 가장 위
        # 2. 링크 태그가 하이라이트보다 위
        # 3. 하이라이트 태그 가장 아래
        self.content_txt.tag_lower("highlight", "link")  # highlight를 link 아래로
        self.content_txt.tag_lower("link", "sel")        # link를 sel 아래로
        self.content_txt.tag_lower("highlight", "sel")   # highlight를 sel 아래로 (중복 방지)
        # ============================================================

        # ===== 텍스트 선택 시 가독성 향상을 위한 스타일 =====
        self.content_txt.configure(
            selectbackground='#347083',  # 선택 배경색 유지
            selectforeground='black',    # 선택 글자색을 검은색으로 변경
            insertbackground='black'     # 커서 색상도 검은색으로 설정
        )
        
        # 선택 관련 이벤트 바인딩 (하이라이트 트리거)
        self.content_txt.bind("<<Selection>>", self.on_content_selection)
        self.content_txt.bind("<ButtonRelease-1>", self.on_content_selection)
        self.content_txt.bind("<Double-Button-1>", self.on_content_selection)
        self.content_txt.bind("<KeyRelease-Shift_L>", self.on_content_selection)
        self.content_txt.bind("<KeyRelease-Shift_R>", self.on_content_selection)

        # ===== 링크 이벤트 바인딩 =====
        # 링크 클릭 이벤트 바인딩 (싱글클릭은 편집만)
        self.content_txt.bind("<Button-1>", self.on_content_click)
        # 더블클릭 시 링크 열기
        self.content_txt.bind("<Double-Button-1>", self.on_content_double_click)
        # 링크 호버 이벤트 (커서 변경)
        self.content_txt.bind("<Motion>", self.on_content_motion)
        
        # 링크 업데이트 타이머 (성능 최적화)
        self.link_update_timer = None
        # ================================================
        
        # ===== SQL 구문 강조 태그 정의 =====
        # SQL 키워드 (파란색 + 볼드체)
        self.content_txt.tag_configure("sql_keyword", foreground="#0000FF", font=("맑은 고딕", 12, "bold"))
        # SQL 문자열 (빨간색)
        self.content_txt.tag_configure("sql_string", foreground="#FF0000")
        # SQL 주석 (회색)
        self.content_txt.tag_configure("sql_comment", foreground="#808080", font=("맑은 고딕", 12, "italic"))
        # SQL 식별자 (테이블/컬럼명 - 초록색)
        self.content_txt.tag_configure("sql_identifier", foreground="#008000")
        
        # SQL 태그 우선순위 (링크 < SQL < 선택)
        self.content_txt.tag_lower("link", "sql_keyword")
        self.content_txt.tag_lower("sql_keyword", "sel")
        self.content_txt.tag_lower("sql_string", "sel")
        self.content_txt.tag_lower("sql_comment", "sel")
        self.content_txt.tag_lower("sql_identifier", "sel")
        
        # SQL 업데이트 타이머
        self.sql_update_timer = None
        # ===================================
        
        # ===== Record 블록 태그 정의 =====
        self.content_txt.tag_configure(
            "record_block",
            font=("Consolas", 11),  # Consolas 폰트 + 11pt
            background="#f5f5f5"    # 옵션: 연한 회색 배경
        )
        # Record 태그 우선순위 (SQL 태그보다 위, 선택 태그보다 아래)
        self.content_txt.tag_lower("record_block", "sql_keyword")
        self.content_txt.tag_lower("record_block", "sel")
        # =================================
        
        # ===== CMD/Terminal 블록 태그 정의 =====
        self.content_txt.tag_configure(
            "cmd_block",
            font=("Consolas", 12),          # Consolas 폰트
            background="black",             # 검은 배경
            foreground="#E0E0E0",            # 약간 회색을 띈 흰색 글자
        )
        # CMD 태그 우선순위 (SQL 태그보다 위, 선택 태그보다 아래)
        self.content_txt.tag_lower("cmd_block", "sql_keyword")
        self.content_txt.tag_lower("cmd_block", "sel")

        # ===== 커서 색상 변경 =====
        def update_cursor_color(event):
            """커서가 CMD 블록 내에 있으면 흰색 커서로 변경"""
            try:
                # 현재 커서 위치 가져오기
                cursor_pos = self.content_txt.index(tk.INSERT)
                # CMD 블록 태그가 적용된 위치인지 확인
                tags = self.content_txt.tag_names(cursor_pos)
                if "cmd_block" in tags:
                    self.content_txt.config(insertbackground="white")  # CMD 영역은 흰색 커서
                    # CMD 블록 내 선택 색상도 개별 설정
                    self.content_txt.configure(selectforeground='white', selectbackground='#555555')
                else:
                    self.content_txt.config(insertbackground="black")  # 일반 영역은 검은색 커서
                    # 일반 영역 선택 색상 복원
                    self.content_txt.configure(selectforeground='black', selectbackground='#347083')
            except:
                self.content_txt.config(insertbackground="black")
                self.content_txt.configure(selectforeground='black', selectbackground='#347083')

        # 커서 이동/클릭/입력 시 색상 업데이트 이벤트 바인딩
        self.content_txt.bind("<Motion>", update_cursor_color)       # 마우스 이동 시
        self.content_txt.bind("<Button-1>", update_cursor_color)     # 클릭 시
        self.content_txt.bind("<KeyPress>", update_cursor_color)     # 키 입력 시
        self.content_txt.bind("<Insert>", update_cursor_color)       # 커서 위치 변경 시

        # ===== Markdown 제목 태그 정의 =====
        self.content_txt.tag_configure("md_h1", font=("맑은 고딕", 20, "bold"), foreground="#2c3e50")  # 제목 1
        self.content_txt.tag_configure("md_h2", font=("맑은 고딕", 16, "bold"), foreground="#34495e")  # 제목 2
        self.content_txt.tag_configure("md_h3", font=("맑은 고딕", 12, "bold"), foreground="#2d3436")  # 제목 3 (선택 시 잘 보이는 색상)
        self.content_txt.tag_configure("md_h4", font=("맑은 고딕", 10, "bold"), foreground="#636e72")  # 제목 4
        self.content_txt.tag_configure("md_h5", font=("맑은 고딕", 9, "bold"), foreground="#636e72")  # 제목 5
        self.content_txt.tag_configure("md_h6", font=("맑은 고딕", 8, "bold"), foreground="#636e72")  # 제목 6

        # Markdown 태그 우선순위 설정 (선택 태그보다 아래)
        self.content_txt.tag_lower("md_h1", "sel")
        self.content_txt.tag_lower("md_h2", "sel")
        self.content_txt.tag_lower("md_h3", "sel")
        self.content_txt.tag_lower("md_h4", "sel")
        self.content_txt.tag_lower("md_h5", "sel")
        self.content_txt.tag_lower("md_h6", "sel")
        
        # ===== Markdown 실시간 반영 이벤트 바인딩 =====
        # self.content_txt.bind("<KeyRelease>", self.on_content_key_release)

        # ================== Catalog 트리 프레임  ==================
        # Catalog 프레임을 중간-카탈로그 PanedWindow에 추가
        self.catalog_frame = ttk.LabelFrame(middle_catalog_paned, text="Catalog", width=200)
        middle_catalog_paned.add(self.catalog_frame, weight=1)

        # ================== Catalog 트리 위젯 생성 (이동된 코드) ==================
        # Catalog 트리에 수평/수직 스크롤바 및 Expand 처리
        catalog_container = ttk.Frame(self.catalog_frame)
        catalog_container.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Grid 레이아웃 설정 (스크롤바가 항상 보이도록)
        catalog_container.grid_rowconfigure(0, weight=1)
        catalog_container.grid_columnconfigure(0, weight=1)
        
        # 수직 스크롤바
        tree_vscroll = ttk.Scrollbar(catalog_container, orient=tk.VERTICAL)
        tree_vscroll.grid(row=0, column=1, sticky="ns")
        
        # 수평 스크롤바
        tree_hscroll = ttk.Scrollbar(catalog_container, orient=tk.HORIZONTAL)
        tree_hscroll.grid(row=1, column=0, sticky="ew")

        # Treeview에서 width 옵션 제거 (ttk.Treeview는 width를 지원하지 않음)
        self.catalog_tree = ttk.Treeview(
            catalog_container,
            yscrollcommand=tree_vscroll.set,
            xscrollcommand=tree_hscroll.set,
            show="tree",  # 열 헤더 숨기기
            selectmode="browse"  # 단일 선택
        )
        
        self.catalog_tree.grid(row=0, column=0, sticky="nsew")
        
        tree_vscroll.config(command=self.catalog_tree.yview)
        tree_hscroll.config(command=self.catalog_tree.xview)
        
        # 스크롤바가 항상 표시되도록 스타일 설정
        style = ttk.Style()
        style.configure("Treeview", rowheight=20)
        # 스크롤바를 항상 표시하도록 설정
        style.layout("Vertical.TScrollbar", 
                     [('Vertical.Scrollbar.trough',
                       {'children': [('Vertical.Scrollbar.thumb', 
                                     {'expand': '1', 'sticky': 'nswe'})],
                        'sticky': 'ns'})])
        style.layout("Horizontal.TScrollbar",
                     [('Horizontal.Scrollbar.trough',
                       {'children': [('Horizontal.Scrollbar.thumb',
                                     {'expand': '1', 'sticky': 'nswe'})],
                        'sticky': 'ew'})])
        
        # Treeview의 자동 스크롤 영역 설정
        self.catalog_tree.configure(
            xscrollcommand=lambda *args: (tree_hscroll.set(*args), tree_hscroll.update()),
            yscrollcommand=lambda *args: (tree_vscroll.set(*args), tree_vscroll.update())
        )
        
        # Catalog 트리 클릭 이벤트 바인딩
        self.catalog_tree.bind("<<TreeviewSelect>>", self.on_catalog_select)
        
        # Catalog 트리 생성 후 자동 Expand 설정
        def expand_all_tree_items(event=None):
            """Catalog 트리의 모든 항목을 자동으로 펼치기"""
            for item in self.catalog_tree.get_children():
                self.catalog_tree.item(item, open=True)
                expand_children(item)
        
        def expand_children(parent_item):
            """하위 항목 재귀적으로 펼치기"""
            for child in self.catalog_tree.get_children(parent_item):
                self.catalog_tree.item(child, open=True)
                expand_children(child)
        
        # 트리 업데이트 후 자동으로 펼치기
        self.root.after(100, expand_all_tree_items)
        
        # Catalog 트리의 크기 변경 이벤트 처리
        def on_catalog_resize(event):
            """Catalog 영역 크기 변경 시 스크롤바 업데이트"""
            self.catalog_tree.update_idletasks()
            tree_hscroll.update()
            tree_vscroll.update()
            
        self.catalog_frame.bind("<Configure>", on_catalog_resize)
        catalog_container.bind("<Configure>", on_catalog_resize)

        # Ctrl+1~6 단축키 바인딩 (이벤트 전파 완전 차단)
        # 오른쪽 Ctrl 별도 바인딩 제거 (Tkinter에서 지원하지 않는 시퀀스)
        for num in range(1, 7):
            # Content 텍스트 위젯에 바인딩
            self.content_txt.bind(f"<Control-{num}>", lambda e, n=num: self.toggle_markdown_header(n, e), add='+')
            self.content_txt.bind(f"<Control-Key-{num}>", lambda e, n=num: self.toggle_markdown_header(n, e), add='+')
            
            # 전체 창에 바인딩 (포커스 상관없이 작동하도록)
            self.root.bind(f"<Control-{num}>", lambda e, n=num: self.toggle_markdown_header(n, e))
            self.root.bind(f"<Control-Key-{num}>", lambda e, n=num: self.toggle_markdown_header(n, e))
          
    def select_all_status(self):
        """모든 상태 체크박스를 선택 상태로 변경"""
        for status, var in self.status_filter_vars.items():
            var.set(True)
        self.apply_status_filter()  # 필터 즉시 적용

    def reset_status_filter(self):
        """상태 필터를 초기 상태로 리셋 (Working, Waiting for cu만 선택)"""
        for status, var in self.status_filter_vars.items():
            # 기본값: Working, Waiting for cu만 True로 설정
            var.set(status in ["Working", "Waiting for cu"])
        self.apply_status_filter()  # 필터 즉시 적용

    def permanently_delete_status_deleted(self):
        # STATUS == "Deleted" 인 노트만 카운트
        delete_targets = [n for n in self.notes if n.get("status") == "Deleted"]

        if not delete_targets:
            messagebox.showinfo("알림", "STATUS: Deleted 인 노트가 없습니다.")
            return

        confirm = messagebox.askyesno(
            "확인",
            f"STATUS: Deleted 노트 {len(delete_targets)}개를\n완전히 영구 삭제합니다.\n정말 삭제하시겠습니까?"
        )
        if not confirm:
            return

        # Deleted 아닌 것만 남기기
        self.notes = [n for n in self.notes if n.get("status") != "Deleted"]

        self.save_to_txt()
        self.apply_all_filters(reset_page=True)
        messagebox.showinfo("완료", f"Deleted 노트 {len(delete_targets)}개 삭제 완료!")

    def on_search_change(self, *args):
        """검색어 변경 시 실시간 필터링 (타이머로 성능 최적화)"""
        # 이전 타이머 취소 (빠른 타이핑 시 중복 실행 방지)
        if self.search_timer:
            self.root.after_cancel(self.search_timer)
        
        # 타이머 시간
        self.search_timer = self.root.after(200, lambda: self.apply_all_filters(reset_page=True))

    # ================== 통합 필터 함수 (검색 + 상태 필터) ==================
    def apply_all_filters(self, reset_page=True):
        """검색 + 상태 필터를 함께 적용하는 통합 함수"""
        # ===== 재귀 호출 방지 =====
        if self.is_applying_filters:
            return
        self.is_applying_filters = True
        # =========================

        try:
            # save_only_if_changed 호출 시 플래그 체크
            if not self.is_saving_changes:
                self.save_only_if_changed()
            
            # 1. 필터 조건 가져오기
            selected_statuses = [status for status, var in self.status_filter_vars.items() if var.get()]
            keyword = self.search_var.get().strip()
            case_sensitive = self.case_sensitive_var.get()
            
            # 2. 필터링 로직
            self.filtered_notes = []
            for note in self.notes:
                # 상태 필터 적용
                note_status = note.get("status", "")
                if note_status not in selected_statuses and note_status != "":
                    continue
                
                # 검색 필터 적용 (검색어가 있을 경우)
                if keyword:
                    # 각 필드별로 개별 처리 + 개행/공백 정리
                    title = note.get("title", "").replace("\n", "").strip()
                    content = note.get("content", "").strip()
                    case_number = note.get("case_number", "").strip()
                    ref_case = note.get("ref_case", "").strip()
                    
                    # 대소문자 구분 여부에 따라 개별 필드 처리
                    if not case_sensitive:
                        keyword_lower = keyword.lower()
                        title_lower = title.lower()
                        content_lower = content.lower()
                        case_number_lower = case_number.lower()
                        ref_case_lower = ref_case.lower()
                        
                        if (keyword_lower not in title_lower and 
                            keyword_lower not in content_lower and 
                            keyword_lower not in case_number_lower and 
                            keyword_lower not in ref_case_lower):
                            continue
                    else:
                        if (keyword not in title and 
                            keyword not in content and 
                            keyword not in case_number and 
                            keyword not in ref_case):
                            continue
                
                # 조건 만족하면 결과에 추가
                self.filtered_notes.append(note)
            
            # 3. 페이지 초기화
            if reset_page:
                self.current_page = 1
            
            self.calculate_pages()
            selected_idx = self.refresh_list()
            self.update_status_label()
            self.update_page_label()
            
            if selected_idx >= 0:
                self._select_list_item(selected_idx)

        finally:
            # ===== 플래그 초기화 =====
            self.is_applying_filters = False
            # =======================

    def apply_search_filter(self):
        """검색 필터 적용 (통합 함수 호출)"""
        # reset_page=True (검색 필터 직접 적용 시 1페이지로 초기화)
        self.apply_all_filters(reset_page=True)

    # ================== 제목/비고 영역 높이 조절 ==================
    def adjust_title_height(self, event=None):
        if hasattr(self, '_title_height_timer'):
            self.root.after_cancel(self._title_height_timer)
        self._title_height_timer = self.root.after(50, self._adjust_title_height_async)

    def _adjust_title_height_async(self):
        try:
            content = self.title_text.get("1.0", tk.END).rstrip("\n")
            if not content:
                self.title_text.config(height=1)
                return

            widget_width = self.title_text.winfo_width()
            if widget_width < 10:
                return

            font_size = 12
            char_width = font_size * 0.45
            max_line_width = widget_width - 20
            
            lines = content.split("\n")
            total_lines = 0
            
            for line in lines:
                if not line:
                    total_lines += 1
                    continue
                
                line_total_width = len(line) * char_width
                if line_total_width <= max_line_width:
                    total_lines += 1
                else:
                    total_lines += int(line_total_width / max_line_width) + 1

            final_height = max(1, min(total_lines, 20))  # 최대 20줄까지
            current_height = int(self.title_text["height"])
            if final_height != current_height:
                self.title_text.config(height=final_height)
                
        except Exception as e:
            self.title_text.config(height=3)

    def adjust_comment_height(self, event=None):
        """비고 영역 높이 동적 조절"""
        if hasattr(self, '_comment_height_timer'):
            self.root.after_cancel(self._comment_height_timer)
        self._comment_height_timer = self.root.after(50, self._adjust_comment_height_async)

    def _adjust_comment_height_async(self):
        try:
            content = self.requester_comment_text.get("1.0", tk.END).rstrip("\n")
            if not content:
                self.requester_comment_text.config(height=2)
                return

            widget_width = self.requester_comment_text.winfo_width()
            if widget_width < 10:
                return

            font_size = 9
            char_width = font_size * 0.45
            max_line_width = widget_width - 20
            
            lines = content.split("\n")
            total_lines = 0
            
            for line in lines:
                if not line:
                    total_lines += 1
                    continue
                
                line_total_width = len(line) * char_width
                if line_total_width <= max_line_width:
                    total_lines += 1
                else:
                    total_lines += int(line_total_width / max_line_width) + 1

            final_height = max(2, min(total_lines, 30))  # 최소 2줄, 최대 30줄
            current_height = int(self.requester_comment_text["height"])
            if final_height != current_height:
                self.requester_comment_text.config(height=final_height)
                
        except Exception as e:
            self.requester_comment_text.config(height=2)

    # ================== Ctrl+Z/Ctrl+Y 기능 ==================
    def undo_title(self, event):
        try:
            self.title_text.edit_undo()
            self.adjust_title_height()
        except tk.TclError:
            pass
        return "break"

    def redo_title(self, event):
        try:
            self.title_text.edit_redo()
            self.adjust_title_height()
        except tk.TclError:
            pass
        return "break"

    def undo_comment(self, event):
        try:
            self.requester_comment_text.edit_undo()
            self.adjust_comment_height()
        except tk.TclError:
            pass
        return "break"

    def redo_comment(self, event):
        try:
            self.requester_comment_text.edit_redo()
            self.adjust_comment_height()
        except tk.TclError:
            pass
        return "break"

    def undo_content(self, event):
        try:
            self.content_txt.edit_undo()
        except tk.TclError:
            pass
        return "break"

    def redo_content(self, event):
        try:
            self.content_txt.edit_redo()
        except tk.TclError:
            pass
        return "break"

    # ================== 줄바꿈 토글 ==================
    def toggle_wrap(self):
        if self.wrap_mode == tk.WORD:
            self.wrap_mode = tk.NONE
            self.wrap_text = "줄바꿈 ON"
        else:
            self.wrap_mode = tk.WORD
            self.wrap_text = "줄바꿈 OFF"
        
        self.content_txt.config(wrap=self.wrap_mode)
        self.wrap_btn.config(text=self.wrap_text)
        self.content_txt.update_idletasks()

    def reset_wrap_mode(self):
        self.wrap_mode = tk.WORD
        self.wrap_text = "줄바꿈 OFF"
        self.content_txt.config(wrap=self.wrap_mode)
        self.wrap_btn.config(text=self.wrap_text)

    # ================== 정렬 토글 기능 ==================
    def toggle_sort(self, sort_by):
        """정렬 방식 토글 + 선택된 메모 페이지로 자동 이동"""
        # 정렬 변경 전 변경사항 자동 저장
        self.save_only_if_changed()
        
        # 정렬 방식 업데이트
        if self.sort_by == sort_by:
            self.sort_order = "asc" if self.sort_order == "desc" else "desc"
        else:
            self.sort_by = sort_by
            self.sort_order = "desc"
        
        # 정렬 버튼 UI 업데이트
        self.update_sort_buttons()
        
        # 선택된 메모가 있으면 해당 메모의 페이지를 찾아 이동
        if self.selected_note_id:
            # 1. 정렬된 노트 목록에서 해당 메모의 페이지 번호 계산
            target_page = self.find_note_page(self.selected_note_id)
            # 2. 현재 페이지를 타겟 페이지로 변경
            self.current_page = target_page
        else:
            # 선택된 메모가 없으면 1페이지로 초기화
            self.current_page = 1
        
        # 페이지 계산 및 리스트 갱신
        self.calculate_pages()
        self.refresh_list()
        self.update_status_label()
        
        # 선택된 메모 하이라이트 유지
        if self.current_id:
            self.highlight_selected_note()

    def update_sort_buttons(self):
        order_text = "ASC" if self.sort_order == "asc" else "DESC"
        
        style = ttk.Style()
        style.configure("Selected.TButton", 
                       foreground="black",
                       background="#ADD8E6",
                       font=("맑은 고딕", 9, "bold"))
        style.configure("Normal.TButton",
                       foreground="black",
                       background="white",
                       font=("맑은 고딕", 9))
        
        for key, btn in self.sort_buttons.items():
            if key == self.sort_by:
                btn_text = {
                    "update": f"수정순 ({order_text})",
                    "create": f"생성순 ({order_text})",
                    "name": f"이름순 ({order_text})"
                }[key]
                btn.config(text=btn_text, style="Selected.TButton")
            else:
                btn_text = {
                    "update": "수정순",
                    "create": "생성순",
                    "name": "이름순"
                }[key]
                btn.config(text=btn_text, style="Normal.TButton")

    # ================== 상태 필터 기능 ==================
    def apply_status_filter(self, event=None):
        """상태 필터 적용 (통합 함수 호출)"""
        # reset_page=True 추가 (필터 변경 시 1페이지로 초기화)
        self.apply_all_filters(reset_page=True)

    # ================== 페이징 기능 (필터된 노트 기준) ==================
    def calculate_pages(self):
        # 필터된 노트를 정렬
        sorted_list = self.sort_notes(self.filtered_notes)
        self.total_pages = max(1, (len(sorted_list) + NOTES_PER_PAGE - 1) // NOTES_PER_PAGE)
        self.update_page_label()

    def update_page_label(self):
        self.page_label.config(text=f"페이지 {self.current_page} / {self.total_pages}")
        self.prev_btn.config(state=tk.NORMAL if self.current_page > 1 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if self.current_page < self.total_pages else tk.DISABLED)

    def prev_page(self):
        if self.current_page > 1:
            self.current_page -= 1
            # 선택된 노트의 페이지와 현재 페이지가 다르면 저장하지 않음
            target_page = self.find_note_page(self.selected_note_id)
            if self.current_page != target_page:
                self.selected_list_index = -1  # 페이지 내 인덱스 초기화
            else:
                # 같은 페이지면 인덱스 유지
                pass
            
            # 리스트 갱신 후 선택된 인덱스 받아오기
            selected_idx = self.refresh_list()
            self.update_page_label()
            
            # 선택된 인덱스가 있으면 선택
            if selected_idx >= 0:
                self._select_list_item(selected_idx)
            else:
                # 다른 페이지이면 ID는 유지하되 인덱스만 초기화
                pass
        
        self.root.update()

    def next_page(self):
        if self.current_page < self.total_pages:
            self.current_page += 1
            # 선택된 노트의 페이지와 현재 페이지가 다르면 저장하지 않음
            target_page = self.find_note_page(self.selected_note_id)
            if self.current_page != target_page:
                self.selected_list_index = -1  # 페이지 내 인덱스 초기화
            else:
                # 같은 페이지면 인덱스 유지
                pass
            
            # 리스트 갱신 후 선택된 인덱스 받아오기
            selected_idx = self.refresh_list()
            self.update_page_label()
            
            # 선택된 인덱스가 있으면 선택
            if selected_idx >= 0:
                self._select_list_item(selected_idx)
            else:
                # 다른 페이지이면 ID는 유지하되 인덱스만 초기화
                pass
        
        self.root.update()

    # ================== 정렬 관련 ==================
    def sort_notes(self, notes_to_sort):
        if self.sort_by == "update":
            sorted_notes = sorted(notes_to_sort, key=lambda x: datetime.strptime(x["update_time"], "%Y-%m-%d %H:%M:%S"),
                                reverse=(self.sort_order == "desc"))
        elif self.sort_by == "create":
            sorted_notes = sorted(notes_to_sort, key=lambda x: datetime.strptime(x["create_time"], "%Y-%m-%d %H:%M:%S"),
                                reverse=(self.sort_order == "desc"))
        elif self.sort_by == "name":
            # 리스트 표시 텍스트에서 |-- 를 제거하고 정렬
            def get_sorting_key(note):
                display_text = self.get_note_list_display_text(note)
                cleaned_text = display_text.replace("|--", "")  # |-- 문자열 제거
                return cleaned_text.strip()  # 양쪽 공백도 정리
            
            sorted_notes = sorted(notes_to_sort, key=get_sorting_key,
                                reverse=(self.sort_order == "desc"))
        else:
            sorted_notes = notes_to_sort
        return sorted_notes

    def get_note_list_display_text(self, note):
        """리스트에 표시될 텍스트 생성"""
        case_number = note.get("case_number", "").strip()
        ref_case = note.get("ref_case", "").strip()
        title = note.get("title", "").strip()
        
        # 표시 텍스트 생성 로직
        if ref_case and case_number:
            display_text = f"|-- {ref_case} << {case_number} -- {title}"
        elif case_number:
            display_text = f"{case_number} -- {title}"
        else:
            display_text = title
        
        return display_text

    def update_status_label(self):
        total_count = len(self.notes)
        filtered_count = len(self.filtered_notes)
        sort_by_text = {"name": "이름순", "update": "수정순", "create": "생성순"}.get(self.sort_by, "수정순")
        sort_order_text = "DESC" if self.sort_order == "desc" else "ASC"
        search = self.search_var.get().strip()
        search_txt = f" | 검색: '{search}'" if search else ""
        
        # 대소문자 구분 표시
        case_txt = " (대소문자 구분)" if self.case_sensitive_var.get() else ""
        
        self.status_label.config(text=f"총 노트 수: {total_count} | 필터된 노트 수: {filtered_count}{search_txt}{case_txt} | 정렬: {sort_by_text} ({sort_order_text})")

    def now_str(self):
        return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    # ================== 템플릿 관리 기능 (파일에서만 읽어오기) ==================
    def init_template_files(self):
        """템플릿 파일 확인 (기존 내용 유지, 생성만 하지 않음)"""
        # 템플릿 파일이 없을 경우 빈 파일 생성
        for template_path in [TEMPLATE_IRD, TEMPLATE_IRD2, TEMPLATE_CLOSURE, TEMPLATE_THNXS]:
            if not os.path.exists(template_path):
                with open(template_path, "w", encoding="utf-8") as f:
                    f.write("")  # 빈 파일만 생성

    def get_template_content(self, template_type):
        """템플릿 파일 내용 읽기 (파일에서만 읽어옴)"""
        template_path = {
            "IRD": TEMPLATE_IRD,
            "IRD2": TEMPLATE_IRD2,
            "Closure": TEMPLATE_CLOSURE,
            "Thnxs": TEMPLATE_THNXS
        }.get(template_type)
        
        if not template_path or not os.path.exists(template_path):
            messagebox.showerror("오류", f"{template_type} 템플릿 파일을 찾을 수 없습니다!")
            return ""
        
        try:
            with open(template_path, "r", encoding="utf-8") as f:
                return f.read()
        except Exception as e:
            messagebox.showerror("오류", f"템플릿 파일 읽기 실패: {str(e)}")
            return ""

    def insert_template(self, template_type):
        """커서 위치에 템플릿 내용 삽입"""
        if not self.current_id:
            messagebox.showinfo("알림", "먼저 노트를 선택하세요!")
            return
        
        # 템플릿 내용 가져오기 (파일에서만 읽어옴)
        template_content = self.get_template_content(template_type)
        if not template_content:
            return
        
        # 현재 노트 정보 가져오기
        case_number = self.case_number_ent.get().strip()
        ref_case = self.ref_case_ent.get().strip()
        title = self.title_text.get("1.0", tk.END).strip()
        status = self.status_combobox.get()
        name = self.requester_name_ent.get().strip()
        role = self.requester_role_ent.get().strip()
        email = self.requester_email_ent.get().strip()
        phone = self.requester_phone_ent.get().strip()
        current_date = self.now_str().split()[0]  # 날짜만
        
        # 변수 치환
        template_content = template_content.replace("{case_number}", case_number)
        template_content = template_content.replace("{ref_case}", ref_case)
        template_content = template_content.replace("{title}", title)
        template_content = template_content.replace("{status}", status)
        template_content = template_content.replace("{name}", name)
        template_content = template_content.replace("{role}", role)
        template_content = template_content.replace("{email}", email)
        template_content = template_content.replace("{phone}", phone)
        template_content = template_content.replace("{current_date}", current_date)
        
        # 커서 위치에 삽입
        cursor_pos = self.content_txt.index(tk.INSERT)
        self.content_txt.insert(cursor_pos, template_content)
        self.content_txt.focus()

        # 템플릿 삽입 후 링크
        self.schedule_link_update()
        
        # SQL 강조
        self.schedule_sql_highlight()
        
        # ===== Record 강조 =====
        self.schedule_record_highlight()

        # ===== CMD 강조 =====
        self.schedule_cmd_highlight()
        
        # ===== XML 강조 =====
        self.schedule_xml_highlight()

        # ===== Markdown 제목 강조를 한 번만 실행 (실시간 업데이트 제거) =====
        #self.highlight_markdown_headers()
    
    # ================== 연락처 관리 기능 ==================
    def load_contacts(self):
        """Contacts.txt에서 연락처 데이터 로드"""
        self.contacts = []
        
        # 파일이 없으면 생성
        if not os.path.exists(CONTACTS_FILE):
            with open(CONTACTS_FILE, "w", encoding="utf-8") as f:
                f.write("")  # 빈 파일 생성
            self.update_requester_combobox()
            return
        
        # 블록 구조로 읽기
        try:
            with open(CONTACTS_FILE, "r", encoding="utf-8") as f:
                content = f.read()
            
            # [CONTACT] 블록 추출
            contact_blocks = re.findall(r'\[CONTACT\](.*?)\[/CONTACT\]', content, re.DOTALL)
            
            for block in contact_blocks:
                contact = {}
                lines = block.splitlines()  # strip() 제거: 원본 공백 유지
                
                for line in lines:
                    # 메타데이터 처리 시만 strip() 적용
                    stripped_line = line.strip()
                    if stripped_line.startswith("ContactID:"):
                        contact["ContactID"] = stripped_line[10:]
                    elif stripped_line.startswith("Name:"):
                        contact["Name"] = stripped_line[5:]
                    elif stripped_line.startswith("Role:"):
                        contact["Role"] = stripped_line[5:]
                    elif stripped_line.startswith("Email:"):
                        contact["Email"] = stripped_line[6:]
                    elif stripped_line.startswith("Phone:"):
                        contact["Phone"] = stripped_line[6:]
                    elif stripped_line.startswith("Comment:"):
                        # Comment 내용 추출 (공백 유지)
                        comment_lines = [line[8:]]  # 원본 line 사용 (strip() 안 함)
                        idx = lines.index(line) + 1
                        while idx < len(lines):
                            next_line = lines[idx]  # strip() 제거
                            if next_line.strip().startswith(("SurveyCount:", "CreateTime:", "UpdateTime:")):
                                break
                            comment_lines.append(next_line)
                            idx += 1
                        contact["Comment"] = "\n".join(comment_lines)  # 공백 유지
                    elif stripped_line.startswith("SurveyCount:"):
                        try:
                            contact["SurveyCount"] = int(stripped_line[12:])
                        except:
                            contact["SurveyCount"] = 0
                    elif stripped_line.startswith("CreateTime:"):
                        contact["CreateTime"] = stripped_line[10:]
                    elif stripped_line.startswith("UpdateTime:"):
                        contact["UpdateTime"] = stripped_line[10:]
                
                # 필수 필드 확인
                if all(k in contact for k in ["ContactID", "Name", "Email"]):
                    # 기본값 설정
                    contact.setdefault("Role", "")
                    contact.setdefault("Phone", "")
                    contact.setdefault("Comment", "")
                    contact.setdefault("SurveyCount", 0)
                    contact.setdefault("CreateTime", self.now_str())
                    contact.setdefault("UpdateTime", self.now_str())
                    self.contacts.append(contact)
            
            # 콤보박스 업데이트
            self.update_requester_combobox()
            
        except Exception as e:
            messagebox.showerror("오류", f"연락처 파일 로드 실패: {str(e)}")

    def update_requester_combobox(self):
        """요청자 콤보박스 업데이트 - 고정 2개 + 나머지 알파벳 정렬"""
        # 고정 옵션
        combo_values = ["--", "📝 신규 요청자 추가"]
        self.contact_id_map = {}

        # 일반 연락처는 알파벳 순 정렬 (Name 기준)
        sorted_contacts = sorted(self.contacts, key=lambda c: c.get("Name", "").lower())

        for contact in sorted_contacts:
            name = contact.get("Name", "")
            role = contact.get("Role", "").strip()
            email = contact.get("Email", "").strip()

            # 직함 + 이메일 둘 다 조건부로 붙임
            parts = [name]
            if role:
                parts.append(f"({role})")
            if email:
                parts.append(f"- {email}")

            display_text = " ".join(parts)
            combo_values.append(display_text)
            self.contact_id_map[display_text] = contact["ContactID"]

        self.requester_combobox['values'] = combo_values
        self.requester_combobox.set("--")

    def load_requester_info(self, event):
        """선택된 요청자 정보 로드"""
        selected_text = self.requester_combobox.get()
        
        # 기본값 -- 선택 시
        if selected_text == "--":
            self.is_new_contact = False
            self.current_contact_id = None
            # 입력 필드 초기화
            self.requester_name_ent.delete(0, tk.END)
            self.requester_role_ent.delete(0, tk.END)
            self.requester_email_ent.delete(0, tk.END)
            self.requester_phone_ent.delete(0, tk.END)
            self.requester_comment_text.delete(1.0, tk.END)
            self.survey_count_ent.delete(0, tk.END)
            self.survey_count_ent.insert(0, "0")
            return
        
        # 신규 요청자 선택 시
        if selected_text == "📝 신규 요청자 추가":
            self.is_new_contact = True
            self.current_contact_id = None
            # 입력 필드 초기화
            self.requester_name_ent.delete(0, tk.END)
            self.requester_role_ent.delete(0, tk.END)
            self.requester_email_ent.delete(0, tk.END)
            self.requester_phone_ent.delete(0, tk.END)
            self.requester_comment_text.delete(1.0, tk.END)
            self.survey_count_ent.delete(0, tk.END)
            self.survey_count_ent.insert(0, "0")
            # 이름 필드에 포커스
            self.requester_name_ent.focus()
            return
        
        # 기존 요청자 선택 시
        self.is_new_contact = False
        if not selected_text or selected_text not in self.contact_id_map:
            return
        
        # ContactID로 연락처 찾기
        contact_id = self.contact_id_map[selected_text]
        self.current_contact_id = contact_id
        
        for contact in self.contacts:
            if contact["ContactID"] == contact_id:
                # 정보 채우기
                self.requester_name_ent.delete(0, tk.END)
                self.requester_name_ent.insert(0, contact["Name"])
                
                self.requester_role_ent.delete(0, tk.END)
                self.requester_role_ent.insert(0, contact["Role"])
                
                self.requester_email_ent.delete(0, tk.END)
                self.requester_email_ent.insert(0, contact["Email"])
                
                self.requester_phone_ent.delete(0, tk.END)
                self.requester_phone_ent.insert(0, contact.get("Phone", ""))
                
                self.requester_comment_text.delete(1.0, tk.END)
                self.requester_comment_text.insert(1.0, contact["Comment"])
                self.adjust_comment_height()
                
                self.survey_count_ent.delete(0, tk.END)
                self.survey_count_ent.insert(0, str(contact["SurveyCount"]))
                break

    def create_new_contact(self):
        """신규 요청자 생성 (이름만 필수 + 오류 추적)"""
        try:
            # 1. 입력값 가져오기 (모든 필드 기본값 처리)
            name = self.requester_name_ent.get().strip()
            
            # 2. 이름만 필수 검증
            if not name:
                messagebox.showerror("오류", "이름은 필수 입력 항목입니다!")
                return None
            
            # 3. ContactID 생성 (강화된 로직)
            max_id = 0
            for contact in self.contacts:
                contact_id = contact.get("ContactID", "")
                if contact_id.startswith("C") and len(contact_id) > 1:
                    try:
                        num = int(contact_id[1:])
                        if num > max_id:
                            max_id = num
                    except:
                        pass  # 잘못된 ID 형식은 무시
            new_contact_id = f"C{max_id + 1:03d}"
            print(f"생성된 ContactID: {new_contact_id}")  # 디버깅용
            
            # 4. 신규 연락처 데이터 (모든 필드 기본값 보장)
            now = self.now_str()
            new_contact = {
                "ContactID": new_contact_id,
                "Name": name,
                "Role": self.requester_role_ent.get().strip() or "",
                "Email": self.requester_email_ent.get().strip() or "",
                "Phone": self.requester_phone_ent.get().strip() or "",
                "Comment": self.requester_comment_text.get(1.0, tk.END).rstrip("\n") or "",
                "SurveyCount": int(self.survey_count_ent.get()) if (self.survey_count_ent.get().strip().isdigit()) else 0,
                "CreateTime": now,
                "UpdateTime": now
            }
            print(f"신규 연락처 데이터: {new_contact}")  # 디버깅용
            
            # 5. 연락처 목록에 추가 + 즉시 저장
            self.contacts.append(new_contact)
            self.save_contacts()  # 저장
            print(f"연락처 목록 총 개수: {len(self.contacts)}")  # 디버깅용
            
            # 6. 콤보박스 즉시 업데이트
            self.update_requester_combobox()
            
            # 7. 상태 변수 업데이트
            self.current_contact_id = new_contact_id
            self.is_new_contact = False
            
            # 8. 성공 메시지
            messagebox.showinfo("성공", f"신규 요청자가 생성되었습니다!\nContactID: {new_contact_id}")
            
            return new_contact_id
        
        except Exception as e:
            # 오류 추적 (터미널에 출력)
            print(f"신규 연락처 생성 오류: {str(e)}")
            messagebox.showerror("오류", f"연락처 생성 중 오류 발생: {str(e)}")
            return None

    def save_contacts(self):
        """Contacts.txt에 저장 (파일 경로 + 권한 확인)"""
        try:
            # 파일 경로 확인
            file_path = os.path.abspath(CONTACTS_FILE)
            print(f"연락처 저장 경로: {file_path}")  # 디버깅용
            
            # 쓰기 권한 확인
            if os.path.exists(file_path):
                if not os.access(file_path, os.W_OK):
                    raise PermissionError("파일에 쓰기 권한이 없습니다")
            
            # 파일 저장
            with open(file_path, "w", encoding="utf-8") as f:
                for contact in self.contacts:
                    f.write("[CONTACT]\n")
                    f.write(f"ContactID:{contact.get('ContactID', '')}\n")
                    f.write(f"Name:{contact.get('Name', '')}\n")
                    f.write(f"Role:{contact.get('Role', '')}\n")
                    f.write(f"Email:{contact.get('Email', '')}\n")
                    f.write(f"Phone:{contact.get('Phone', '')}\n")
                    f.write(f"Comment:{contact.get('Comment', '')}\n")
                    f.write(f"SurveyCount:{contact.get('SurveyCount', 0)}\n")
                    f.write(f"CreateTime:{contact.get('CreateTime', self.now_str())}\n")
                    f.write(f"UpdateTime:{contact.get('UpdateTime', self.now_str())}\n")
                    f.write("[/CONTACT]\n\n")
            
            print("연락처 파일 저장 성공")  # 디버깅용
            
        except PermissionError:
            messagebox.showerror("오류", f"{file_path}에 쓰기 권한이 없습니다!\n관리자 권한으로 실행해주세요.")
        except Exception as e:
            print(f"연락처 저장 오류: {str(e)}")  # 디버깅용
            messagebox.showerror("오류", f"연락처 저장 실패: {str(e)}")

    def update_contact(self):
        """기존 연락처 정보 업데이트"""
        if not self.current_contact_id:
            return
        
        # 입력값 가져오기
        try:
            updated_data = {
                "Name": self.requester_name_ent.get().strip(),
                "Role": self.requester_role_ent.get().strip(),
                "Email": self.requester_email_ent.get().strip(),
                "Phone": self.requester_phone_ent.get().strip(),
                "Comment": self.requester_comment_text.get(1.0, tk.END).rstrip("\n"),
                "SurveyCount": int(self.survey_count_ent.get()) if self.survey_count_ent.get().strip() else 0,
                "UpdateTime": self.now_str()
            }
        except ValueError:
            messagebox.showerror("오류", "Survey Count는 숫자여야 합니다")
            return
        
        # 연락처 찾아서 업데이트
        for idx, contact in enumerate(self.contacts):
            if contact["ContactID"] == self.current_contact_id:
                # 변경 여부 확인
                is_changed = (
                    updated_data["Name"] != contact["Name"] or
                    updated_data["Role"] != contact["Role"] or
                    updated_data["Email"] != contact["Email"] or
                    updated_data["Phone"] != contact.get("Phone", "") or
                    updated_data["Comment"] != contact["Comment"] or
                    updated_data["SurveyCount"] != contact["SurveyCount"]
                )
                
                if is_changed:
                    self.contacts[idx].update(updated_data)
                    # Contacts.txt 저장
                    self.save_contacts()
                    # 콤보박스 업데이트
                    self.update_requester_combobox()
                break

    # ================== 파일 저장/로드 ==================
    def load_from_txt(self):
        self.notes = []
        if not os.path.exists(SAVE_FILE):
            self.update_status_label()
            return
        
        try:
            with open(SAVE_FILE, "r", encoding="utf-8") as f:
                data = f.read()

            blocks = data.split("[NOTE]")[1:]
            for b in blocks:
                if "[/NOTE]" not in b:
                    continue
                body = b.split("[/NOTE]")[0]  # strip() 제거: 원본 공백 유지
                note = {}
                lines = body.splitlines()
                content_lines = []
                content_started = False
                
                for line in lines:
                    # strip() 제거 → 원본 라인 유지
                    # line = line.strip()  # 이 줄 삭제 또는 주석 처리
                    
                    # 메타데이터 처리 시만 필요한 부분에 strip() 적용
                    if line.startswith("ID:"):
                        note["id"] = int(line[3:].strip())  # 값만 strip()
                    elif line.startswith("TITLE:"):
                        note["title"] = line[6:]  # 제목은 공백 유지
                    elif line.startswith("CONTENT:"):
                        content_started = True
                        content_lines.append(line[8:])  # 내용 공백 유지
                    elif line.startswith("CREATE:"):
                        content_started = False
                        note["create_time"] = line[7:].strip()  # 값만 strip()
                    elif line.startswith("UPDATE:"):
                        note["update_time"] = line[7:].strip()  # 값만 strip()
                    elif line.startswith("DELETED:"):
                        note["deleted"] = line[8:].strip()  # 값만 strip()
                    elif line.startswith("CASE_NUMBER:"):
                        note["case_number"] = line[12:].strip()  # 값만 strip()
                    elif line.startswith("REF_CASE:"):
                        note["ref_case"] = line[9:].strip()  # 값만 strip()
                    elif line.startswith("STATUS:"):
                        note["status"] = line[7:].strip()  # 값만 strip()
                    elif line.startswith("CONTACT_ID:"):
                        note["contact_id"] = line[11:].strip()  # 값만 strip()
                    elif content_started:
                        content_lines.append(line)  # 내용 라인은 그대로 추가
                
                note["content"] = "\n".join(content_lines)  # 줄바꿈 + 공백 유지
                
                # 필수 필드 확인
                required_fields = ["id","title","content","create_time","update_time"]
                if all(k in note for k in required_fields):
                    # 옵션 필드 기본값 설정
                    note.setdefault("case_number", "")
                    note.setdefault("ref_case", "")
                    note.setdefault("status", "")
                    note.setdefault("contact_id", "")
                    note.setdefault("deleted", "no")  # 기본값 no
                    self.notes.append(note)
                    
        except Exception as e:
            messagebox.showerror("오류", f"노트 파일 로드 실패: {str(e)}")
            
        self.update_status_label()
        self.update_sort_buttons()

    def save_to_txt(self):
        # ===== 재귀 호출 방지 =====
        if self.is_saving:
            return
        self.is_saving = True
        # =========================

        try:
            with open(SAVE_FILE, "w", encoding="utf-8") as f:
                for n in self.notes:
                    f.write("[NOTE]\n")
                    f.write(f"ID:{n['id']}\n")
                    f.write(f"TITLE:{n['title']}\n")
                    f.write(f"CONTENT:{n['content']}\n")
                    f.write(f"CREATE:{n['create_time']}\n")
                    f.write(f"UPDATE:{n['update_time']}\n")
                    f.write(f"DELETED:{n.get('deleted', 'no')}\n")
                    f.write(f"CASE_NUMBER:{n.get('case_number', '')}\n")
                    f.write(f"REF_CASE:{n.get('ref_case', '')}\n")
                    f.write(f"STATUS:{n.get('status', '')}\n")
                    f.write(f"CONTACT_ID:{n.get('contact_id', '')}\n")
                    f.write("[/NOTE]\n\n")
        except Exception as e:
            messagebox.showerror("오류", f"저장 실패: {str(e)}")
        finally:
            # 플래그 초기화
            self.is_saving = False
                
        # 필터 다시 적용 (플래그 체크)
        if not self.is_applying_filters:
            self.update_status_label()

    def refresh_list(self):
        """리스트 갱신 (선택된 페이지에서만 하이라이트 유지)"""
        # 1. 전역으로 저장된 선택 정보 불러오기
        target_id = self.selected_note_id
        highlight_idx = -1
        target_note = None

        # 2. 리스트 초기화
        self.listbox.delete(0, tk.END)
        
        # 3. 필터+정렬된 노트 가져오기
        sorted_list = self.sort_notes(self.filtered_notes)
        start_idx = (self.current_page - 1) * NOTES_PER_PAGE
        end_idx = start_idx + NOTES_PER_PAGE
        page_notes = sorted_list[start_idx:end_idx]
        
        # 4. 리스트에 항목 추가 + 선택된 ID의 인덱스/노트 찾기
        for idx, note in enumerate(page_notes):
            display_text = self.get_note_list_display_text(note)
            self.listbox.insert(tk.END, display_text)
            
            # 선택된 ID와 일치하면 인덱스+노트 저장 (현재 페이지 내에서만)
            if note.get("id") == target_id:
                highlight_idx = idx
                target_note = note

        # 5. 하이라이트 적용 (현재 페이지에 있는 경우만)
        if highlight_idx >= 0:
            # 모든 항목 색상 초기화
            for i in range(self.listbox.size()):
                self.listbox.itemconfig(i, bg='white', fg='black')
            
            # 선택된 항목만 강조
            self.listbox.itemconfig(highlight_idx, bg='#347083', fg='white')
            self.listbox.selection_set(highlight_idx)
            self.listbox.activate(highlight_idx)
            self.listbox.see(highlight_idx)
            self.selected_list_index = highlight_idx
            
            # 현재 페이지의 노트만 UI에 로드
            if target_note and self.current_id != target_id:
                self.current_id = target_id
                self.load_note_to_ui(target_note)
        else:
            # 현재 페이지에 선택된 노트가 없으면 하이라이트만 초기화 (ID는 유지)
            for i in range(self.listbox.size()):
                self.listbox.itemconfig(i, bg='white', fg='black')
            self.selected_list_index = -1
            # 다른 페이지이면 current_id는 유지하되 UI 로드는 하지 않음

        # 6. UI 업데이트
        self.listbox.update_idletasks()
        self.root.update()

        # 리스트박스 수평 스크롤을 항상 왼쪽으로 초기화
        self.listbox.xview_moveto(0)  # 수평 스크롤을 왼쪽으로 초기화
        self.listbox.yview_moveto(0)  # 수직 스크롤도 맨 위로 초기화 (선택 사항)

        # 리스트박스 너비 자동 조절 기능 제거 (고정 너비 유지)
        # 기존 자동 조절 코드 삭제
        # if self.listbox.size() > 0:
        #     max_width = max(len(self.listbox.get(i)) for i in range(self.listbox.size()))
        #     self.listbox.config(width=min(max_width + 2, 80))

        # 7. 인덱스 반환 (페이징용)
        return highlight_idx

    # 하이라이트 보조 메서드
    def _force_highlight(self):
        """하이라이트를 적용 (새 노트에만 하이라이트 유지)"""
        if not self.selected_note_id:
            return
        
        # 1. 모든 리스트 항목의 하이라이트 초기화
        for i in range(self.listbox.size()):
            self.listbox.itemconfig(i, bg='white', fg='black')
        
        # 2. 현재 페이지에서 새 노트의 인덱스를 찾아 하이라이트
        sorted_list = self.sort_notes(self.filtered_notes)
        start_idx = (self.current_page - 1) * NOTES_PER_PAGE
        end_idx = start_idx + NOTES_PER_PAGE
        page_notes = sorted_list[start_idx:end_idx]
        
        for idx, note in enumerate(page_notes):
            if note["id"] == self.selected_note_id:
                self.listbox.selection_clear(0, tk.END)
                self.listbox.selection_set(idx)
                self.listbox.itemconfig(idx, bg='#347083', fg='white')
                self.listbox.activate(idx)
                self.listbox.see(idx)
                break
        
        # 3. UI 업데이트
        self.listbox.update_idletasks()
        self.root.update()

    def highlight_selected_note(self):
        """선택된 ID의 메모를 현재 페이지에서 하이라이트 (강력한 버전)"""
        if not self.current_id:
            self.listbox.selection_clear(0, tk.END)
            return
        
        # 1. 현재 페이지의 노트 목록을 다시 가져오기 (정렬+필터 적용)
        sorted_notes = self.sort_notes(self.filtered_notes)
        start_idx = (self.current_page - 1) * NOTES_PER_PAGE
        end_idx = start_idx + NOTES_PER_PAGE
        current_page_notes = sorted_notes[start_idx:end_idx]
        
        # 2. 현재 페이지에서 해당 ID 찾기
        target_index = -1
        for idx, note in enumerate(current_page_notes):
            if note.get("id") == self.current_id:
                target_index = idx
                break
        
        # 3. 하이라이트 적용 (UI 업데이트 포함)
        if target_index >= 0:
            # UI 업데이트를 실행
            self.listbox.update_idletasks()
            
            # 선택 상태 초기화 후 재설정
            self.listbox.selection_clear(0, tk.END)
            self.listbox.selection_set(target_index)
            self.listbox.activate(target_index)  # 활성화 (하이라이트 핵심)
            self.listbox.see(target_index)       # 화면에 보이도록 스크롤
            self.listbox.focus_set()             # 리스트박스에 포커스
            
            # 선택된 항목의 배경색 지정 (tkinter 기본 리스트박스용)
            self.listbox.itemconfig(target_index, {'bg': '#347083', 'fg': 'white'})
        else:
            # 현재 페이지에 없으면 선택 초기화
            self.current_id = None
            self.listbox.selection_clear(0, tk.END)
        
        # 최종 UI 업데이트
        self.root.update_idletasks()

    # 리스트 선택을 안정적으로 처리하는 보조 메서드
    def _set_list_selection(self, idx):
        """리스트 선택을 안정적으로 설정"""
        try:
            self.listbox.selection_clear(0, tk.END)
            self.listbox.selection_set(idx)
            self.listbox.see(idx)
            self.listbox.activate(idx)  # 선택된 항목을 활성화
        except:
            pass

    # ================== 노트 생성 ==================
    def create_new_note(self):
        now = self.now_str()
        new_id = max((n["id"] for n in self.notes), default=0) + 1

        new_note = {
            "id": new_id,
            "title": "New Note",
            "content": "",
            "create_time": now,
            "update_time": now,
            "deleted": "no",
            "case_number": "",
            "ref_case": "",
            "status": "Working",
            "contact_id": ""
        }

        self.notes.append(new_note)
        self.save_to_txt()

        # 1. 필터 적용 (1페이지 초기화) + 필터된 목록 갱신 완료 후 진행
        self.apply_all_filters(reset_page=True)
        
        # 2. 필터된 목록에 새 노트가 포함된 상태에서 페이지 계산
        if not any(n["id"] == new_id for n in self.filtered_notes):
            self.filtered_notes.append(new_note)
        
        # 3. 새 노트의 페이지를 정확히 계산 (필터된 목록 기준)
        target_page = self.find_note_page(new_id)
        self.current_page = target_page  # 새 노트 페이지로 이동
        self.calculate_pages()  # 페이지 수 재계산
        
        # 4. 선택 상태 초기화 (기존 하이라이트 제거)
        self.selected_note_id = new_id  # 선택된 ID를 새 노트로 설정
        self.current_id = new_id        # 현재 편집 ID도 새 노트로 설정
        self.selected_list_index = -1   # 기존 인덱스 초기화
        
        # 5. 리스트 갱신 + 새 노트에 하이라이트 적용
        self.refresh_list()  # 새 페이지의 리스트를 불러오고
        self.highlight_selected_note()  # 새 노트에 하이라이트 적용
        
        # 6. UI 초기화 (새 노트 정보로 설정)
        self.title_text.delete(1.0, tk.END)
        self.title_text.insert(1.0, new_note["title"])
        self.content_txt.delete(1.0, tk.END)

        self.case_number_ent.delete(0, tk.END)
        self.ref_case_ent.delete(0, tk.END)
        self.status_combobox.set("Working")

        self.requester_combobox.set("--")
        self.requester_name_ent.delete(0, tk.END)
        self.requester_role_ent.delete(0, tk.END)
        self.requester_email_ent.delete(0, tk.END)
        self.requester_phone_ent.delete(0, tk.END)
        self.requester_comment_text.delete(1.0, tk.END)
        self.survey_count_ent.delete(0, tk.END)
        self.survey_count_ent.insert(0, "0")
        self.current_contact_id = None
        self.is_new_contact = False

        self.title_text.focus()
        self.adjust_title_height()
        self.reset_wrap_mode()
        
        # 하이라이트 초기화 (새 노트 생성 시)
        self.content_txt.tag_remove("highlight", "1.0", tk.END)
        self.last_selected_text = ""
        # 태그 우선순위 재설정
        self.content_txt.tag_lower("highlight", "sel")
        
        # 링크 업데이트
        self.schedule_link_update()

        self.original_title = self.title_text.get(1.0, tk.END).strip()
        self.original_content = self.content_txt.get(1.0, tk.END)[:-1]

        self.save_only_if_changed()
        
        # 최종 보장: 리스트를 다시 갱신하고 하이라이트 적용
        self.root.after(100, self._force_highlight)  # 0.1초 후 하이라이트
        
        # SQL 강조 초기화
        self.schedule_sql_highlight()
        
        # Record 강조 초기화
        self.schedule_record_highlight()
        
        # CMD 강조 업데이트
        self.schedule_cmd_highlight()

        # XML 강조 업데이트
        self.schedule_xml_highlight()

        # 새 노트 생성 시 Markdown 렌더링 제거
        # self.highlight_markdown_headers() 호출 삭제

        # Catalog 트리 초기화
        self.update_catalog_tree()
        
        self.root.after(100, self.update_catalog_tree)

    def load_note_to_ui(self, note):
        """노트 정보 로드"""
        # 기본 정보 로드
        self.id_ent.config(state="normal")
        self.id_ent.delete(0, tk.END)
        self.id_ent.insert(0, note["id"])
        self.id_ent.config(state="readonly")

        self.create_ent.config(state="normal")
        self.create_ent.delete(0, tk.END)
        self.create_ent.insert(0, note["create_time"])
        self.create_ent.config(state="readonly")

        self.update_ent.config(state="normal")
        self.update_ent.delete(0, tk.END)
        self.update_ent.insert(0, note["update_time"])
        self.update_ent.config(state="readonly")

        self.title_text.delete(1.0, tk.END)
        self.title_text.insert(1.0, note["title"])
        self.adjust_title_height()

        self.content_txt.delete(1.0, tk.END)
        self.content_txt.insert(1.0, note["content"])

        # 케이스 정보 로드
        self.case_number_ent.delete(0, tk.END)
        self.case_number_ent.insert(0, note.get("case_number", ""))
        
        self.ref_case_ent.delete(0, tk.END)
        self.ref_case_ent.insert(0, note.get("ref_case", ""))
        
        self.status_combobox.set(note.get("status", ""))

        # 요청자 정보 로드
        contact_id = note.get("contact_id", "")
        self.current_contact_id = contact_id
        self.is_new_contact = False
        
        # ContactID로 연락처 찾기
        if contact_id:
            for contact in self.contacts:
                if contact["ContactID"] == contact_id:
                    # 콤보박스 선택
                    display_text = f"{contact['Name']} ({contact['Role']}) - {contact['Email']}"
                    self.requester_combobox.set(display_text)
                    
                    # 상세 정보 채우기
                    self.requester_name_ent.delete(0, tk.END)
                    self.requester_name_ent.insert(0, contact["Name"])
                    
                    self.requester_role_ent.delete(0, tk.END)
                    self.requester_role_ent.insert(0, contact["Role"])
                    
                    self.requester_email_ent.delete(0, tk.END)
                    self.requester_email_ent.insert(0, contact["Email"])
                    
                    self.requester_phone_ent.delete(0, tk.END)
                    self.requester_phone_ent.insert(0, contact.get("Phone", ""))
                    
                    self.requester_comment_text.delete(1.0, tk.END)
                    self.requester_comment_text.insert(1.0, contact["Comment"])
                    self.adjust_comment_height()
                    
                    self.survey_count_ent.delete(0, tk.END)
                    self.survey_count_ent.insert(0, str(contact["SurveyCount"]))
                    break
        else:
            # 연락처가 없는 경우 초기화
            self.requester_combobox.set("--")
            self.requester_name_ent.delete(0, tk.END)
            self.requester_role_ent.delete(0, tk.END)
            self.requester_email_ent.delete(0, tk.END)
            self.requester_phone_ent.delete(0, tk.END)
            self.requester_comment_text.delete(1.0, tk.END)
            self.survey_count_ent.delete(0, tk.END)
            self.survey_count_ent.insert(0, "0")
            self.is_new_contact = False

        self.original_title = note["title"].strip()
        self.original_content = note["content"]

    # ================== 노트 전환 ==================
    def switch_note(self, event):
        selections = self.listbox.curselection()
        if not selections:
            self.selected_note_id = None
            self.selected_list_index = -1
            return
        
        idx = selections[0]
        self.save_only_if_changed()  # 노트 전환 시 무조건 변경사항 저장 (Ref. Case 포함)

        sorted_filtered = self.sort_notes(self.filtered_notes)
        total_idx = (self.current_page - 1) * NOTES_PER_PAGE + idx
        if total_idx >= len(sorted_filtered):
            self.selected_note_id = None
            self.selected_list_index = -1
            return

        note = sorted_filtered[total_idx]
        self.current_id = note["id"]
        self.selected_note_id = note["id"]  # 선택된 ID 저장
        self.selected_list_index = idx     # 현재 페이지 내 인덱스 저장
        self.load_note_to_ui(note)

        # 하이라이트 (색상 직접 지정)
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(idx)
        self.listbox.activate(idx)
        self.listbox.see(idx)
        self.listbox.focus_set()
        
        # 모든 항목 색상 초기화 후 선택된 항목만 강조
        for i in range(self.listbox.size()):
            if i == idx:
                self.listbox.itemconfig(i, bg='#347083', fg='white')
            else:
                self.listbox.itemconfig(i, bg='white', fg='black')
        
        self.reset_wrap_mode()
        
        # 하이라이트 초기화 (노트 전환 시)
        self.content_txt.tag_remove("highlight", "1.0", tk.END)
        self.last_selected_text = ""
        # 태그 우선순위 재설정
        self.content_txt.tag_lower("highlight", "sel")

        # 링크 업데이트
        self.schedule_link_update()

        # SQL 강조
        self.schedule_sql_highlight()
        
        # Record 강조
        self.schedule_record_highlight()
        
        # CMD 강조
        self.schedule_cmd_highlight()
        
        # XML 강조
        self.schedule_xml_highlight()

        # Catalog 트리 즉시 업데이트 (노트 전환 시)
        self.update_catalog_tree()
        
        # ✅ 노트 전환/오픈 시에만 Markdown 렌더링 실행
        self.root.after(1000, self.highlight_markdown_headers)
        
        self.root.after(100, self.update_catalog_tree)
        
    # ================== 변경 시에만 저장 ==================
    def save_only_if_changed(self):
        # ===== 재귀 호출 방지 =====
        if self.is_saving_changes:
            return
        self.is_saving_changes = True
        # =========================

        try:
            if self.current_id is None and self.selected_note_id is not None:
                self.current_id = self.selected_note_id
                
            if self.current_id is None:
                return

            current_title = self.title_text.get(1.0, tk.END).strip()
            current_content = self.content_txt.get(1.0, tk.END)[:-1]
            
            # 케이스 정보 가져오기
            current_case_number = self.case_number_ent.get().strip()
            current_ref_case = self.ref_case_ent.get().strip()
            current_status = self.status_combobox.get().strip() or "Working"
            current_contact_id = self.current_contact_id or ""

            # 변경 여부 확인 (Ref. Case 포함)
            is_changed = False
            for n in self.notes:
                if n["id"] == self.current_id:
                    if (current_title != n["title"] or 
                        current_content != n["content"] or
                        current_case_number != n.get("case_number", "") or
                        current_ref_case != n.get("ref_case", "") or
                        current_status != n.get("status", "") or
                        current_contact_id != n.get("contact_id", "")):
                        is_changed = True
                    break

            # 신규 연락처인 경우 무조건 생성
            new_contact_created = False
            if self.is_new_contact:
                new_contact_id = self.create_new_contact()
                if new_contact_id:
                    current_contact_id = new_contact_id
                    self.current_contact_id = new_contact_id
                    new_contact_created = True
                    is_changed = True  # 변경된 것으로 처리하여 저장
            
            if not is_changed and not new_contact_created:
                if not self.is_new_contact:
                    self.update_contact()
                return

            # 변경된 경우 저장
            now = self.now_str()
            for n in self.notes:
                if n["id"] == self.current_id:
                    n["title"] = current_title if current_title else "New Note"
                    n["content"] = current_content
                    n["update_time"] = now
                    n["case_number"] = current_case_number
                    n["ref_case"] = current_ref_case
                    n["status"] = current_status
                    n["contact_id"] = current_contact_id
                    break

            # 기존 연락처 업데이트
            if not self.is_new_contact:
                self.update_contact()
            
            # save_to_txt 호출 (플래그로 보호됨)
            self.save_to_txt()
            self.calculate_pages()
            
            # apply_all_filters 호출 시 플래그 체크
            if not self.is_applying_filters:
                self.apply_all_filters(reset_page=False)
            
            # 선택된 노트 하이라이트
            self.highlight_selected_note()

            # 저장 후 링크/강조
            self.schedule_link_update()
            self.schedule_sql_highlight()
            self.schedule_record_highlight()
            self.schedule_cmd_highlight()
            self.schedule_xml_highlight()
            
            # 저장 시 Markdown 렌더링 호출 완전 제거
            # self.schedule_markdown_highlight()

        finally:
            # ===== 플래그 초기화 =====
            self.is_saving_changes = False
            # =======================

    def _select_list_item(self, idx):
        """리스트 항목을 선택 (저장 로직 포함)"""
        try:
            # ==== 전환 전에 변경사항 저장 ====
            self.save_only_if_changed()
            # ===========================================
            
            # 1. 기본 선택 상태 설정
            self.listbox.selection_clear(0, tk.END)
            self.listbox.selection_set(idx)
            self.listbox.activate(idx)
            self.listbox.see(idx)
            
            # 2. 시각적 하이라이트 (배경/글자색 직접 변경)
            self.listbox.itemconfig(idx, {'bg': '#347083', 'fg': 'white'})
            for i in range(self.listbox.size()):
                if i != idx:
                    self.listbox.itemconfig(i, {'bg': 'white', 'fg': 'black'})
            
            # 3. tkinter 내부 선택 이벤트 발생
            self.listbox.event_generate("<<ListboxSelect>>")
            
            # 4. 포커스 및 UI 업데이트
            self.listbox.focus_set()
            self.listbox.update_idletasks()
            self.root.update()
            
        except Exception as e:
            print(f"선택 오류: {e}")

    def find_note_page(self, note_id):
        """주어진 노트 ID가 있는 페이지를 찾아 반환 (없으면 1페이지)"""
        if not note_id or not self.filtered_notes:
            return 1
        
        # 필터+정렬된 노트 목록에서 ID 위치 찾기
        sorted_list = self.sort_notes(self.filtered_notes)
        note_index = -1
        
        for idx, note in enumerate(sorted_list):
            if note.get("id") == note_id:
                note_index = idx
                break
        
        # ID가 없으면 1페이지 반환
        if note_index == -1:
            return 1
        
        # 페이지 번호 계산 (NOTES_PER_PAGE는 페이지당 노트 수)
        page_number = (note_index // NOTES_PER_PAGE) + 1
        return page_number

    # ================== 텍스트 하이라이트 기능 (안정화 버전) ==================
    def on_content_selection(self, event=None):
        """텍스트 선택 시 디바운싱 처리 후 하이라이트 업데이트"""
        # 이벤트 발생 직후 바로 처리 (타이머 제거로 반응성 향상)
        self.root.after_idle(self.update_content_highlight)  # UI가 유휴 상태일 때 실행

    def update_content_highlight(self):
        """선택된 텍스트와 동일한 내용을 모두 하이라이트"""
        # 중복 처리 방지 + 빠른 반환 조건 강화
        if self.is_highlight_processing:
            return
        
        self.is_highlight_processing = True
        
        try:
            # 1. 선택된 텍스트 가져오기 (강화된 예외 처리)
            selected_text = ""
            try:
                # 선택 영역이 실제로 존재하는지 확인
                if self.content_txt.tag_ranges("sel"):
                    selected_start = self.content_txt.index(tk.SEL_FIRST)
                    selected_end = self.content_txt.index(tk.SEL_LAST)
                    selected_text = self.content_txt.get(selected_start, selected_end).strip()
            except (tk.TclError, IndexError):
                # 선택 영역이 없는 경우 초기화
                self.content_txt.tag_remove("highlight", "1.0", tk.END)
                self.last_selected_text = ""
                self.is_highlight_processing = False
                return
            
            # 2. 빈 텍스트 또는 너무 짧은 텍스트 (1글자 이하) 처리하지 않음
            if not selected_text or len(selected_text) < 2:
                self.content_txt.tag_remove("highlight", "1.0", tk.END)
                self.last_selected_text = ""
                self.is_highlight_processing = False
                return
            
            # 3. 이전과 동일한 텍스트는 처리하지 않음
            if selected_text == self.last_selected_text:
                self.is_highlight_processing = False
                return
            
            self.last_selected_text = selected_text
            
            # 4. 성능 제한: 너무 긴 텍스트는 처리하지 않음
            full_text = self.content_txt.get("1.0", tk.END)
            #if len(full_text) > 10000 or len(selected_text) > 100:
            #    self.is_highlight_processing = False
            #    return
            
            # 5. 기존 하이라이트 먼저 제거
            self.content_txt.tag_remove("highlight", "1.0", tk.END)
            
            # 6. 선택 영역 정보 저장 (절대 위치 대신 직접 비교)
            sel_start = self.content_txt.index(tk.SEL_FIRST)
            sel_end = self.content_txt.index(tk.SEL_LAST)
            
            # 7. 정규식으로 모든 동일 텍스트 찾기 (대소문자 구분 없음)
            import re
            # 특수 문자 이스케이프 처리
            pattern = re.escape(selected_text)
            # 전체 텍스트에서 모든 매치 찾기
            text_content = self.content_txt.get("1.0", tk.END)
            matches = list(re.finditer(pattern, text_content))
            
            # 8. 각 매치에 하이라이트 적용 (선택 영역 제외)
            for match in matches:
                match_start = match.start()
                match_end = match.end()
                
                # 절대 위치 -> Tkinter 인덱스 변환
                start_idx = self.absolute_to_text_index(match_start)
                end_idx = self.absolute_to_text_index(match_end)
                
                # 선택 영역 내에 있는지 확인 (내부가 아니면 하이라이트)
                if not (self.is_position_between(start_idx, sel_start, sel_end) and 
                        self.is_position_between(end_idx, sel_start, sel_end)):
                    self.content_txt.tag_add("highlight", start_idx, end_idx)
            
            # 9. 하이라이트 태그 우선순위 강화 (선택 태그보다 항상 아래에 위치)
            self.content_txt.tag_lower("highlight", "sel")
            
        except Exception as e:
            print(f"하이라이트 오류: {e}")
        finally:
            self.is_highlight_processing = False

    def is_position_between(self, pos, start, end):
        """Tkinter 인덱스(pos)가 start와 end 사이에 있는지 확인"""
        try:
            return self.content_txt.compare(pos, ">=", start) and self.content_txt.compare(pos, "<=", end)
        except:
            return False

    def text_index_to_absolute(self, index_str):
        """Tkinter 인덱스 -> 절대 위치 변환 (안정화 버전)"""
        try:
            # Tkinter 내장 메서드로 라인/컬럼 가져오기
            line, col = map(int, index_str.split('.'))
            abs_pos = 0
            
            # 1줄씩 계산 (예외 처리)
            for i in range(1, line):
                try:
                    line_text = self.content_txt.get(f"{i}.0", f"{i}.end")
                    abs_pos += len(line_text) + 1  # +1은 줄바꿈 문자
                except:
                    pass
            
            abs_pos += col
            return abs_pos
        except:
            return 0

    def absolute_to_text_index(self, absolute_pos):
        """절대 문자 위치를 tkinter Text 위젯의 "line.column" 형식 인덱스로 변환"""
        full_text = self.content_txt.get("1.0", "end-1c")
        
        # 위치가 텍스트 길이를 넘어가면 마지막 위치로 설정
        if absolute_pos >= len(full_text):
            return "end-1c"
        
        # 줄 수와 컬럼 수 계산
        line_num = 1
        current_pos = 0
        
        for char in full_text[:absolute_pos]:
            if char == '\n':
                line_num += 1
                current_pos = 0
            else:
                current_pos += 1
        
        return f"{line_num}.{current_pos}"

    # ================== 링크 기능 관련 메서드 ==================
    def extract_urls(self, text):
        """텍스트에서 URL을 추출하는 정규식 함수 (서브도메인 완전 지원)"""
        # 강화된 URL 패턴: 긴 서브도메인(qacvecodebeamer.volvo.net) 완전 지원
        url_pattern = r'''
            (?:https?://|ftp://|www\.)?          # 프로토콜 선택적
            (?:[a-zA-Z0-9-]+\.)+                # 서브도메인 여러 개 지원 (예: qacvecodebeamer.volvo.)
            (?:com|net|org|kr|co\.kr|io|gov|edu|biz|info|me|us|uk|jp|dev|cn)  # 최상위 도메인
            (?:/[^\s<>"]*)?                     # 경로 선택적
        '''
        urls = re.findall(url_pattern, text, re.VERBOSE | re.IGNORECASE)
        
        # .java:숫자 형식 제외 + 빈 문자열 제거
        urls = [
            url.strip() for url in urls
            if url.strip() and not re.search(r'\.java:\d+', url, re.IGNORECASE)
        ]
        
        # 중복 제거 (순서 유지)
        seen = set()
        unique_urls = []
        for url in urls:
            if url not in seen:
                seen.add(url)
                unique_urls.append(url)
        
        return unique_urls

    def update_links(self):
        """내용 영역의 URL을 링크 태그로 표시"""
        # 기존 링크 태그 제거
        self.content_txt.tag_remove("link", "1.0", tk.END)
        
        # 전체 텍스트 가져오기
        full_text = self.content_txt.get("1.0", tk.END)
        if not full_text:
            return
        
        # URL 추출
        urls = self.extract_urls(full_text)
        if not urls:
            return
        
        # 각 URL에 링크 태그 적용 (문제 해결 핵심: unique tag 사용)
        for idx, url in enumerate(urls):
            # 고유한 링크 태그 이름 생성 (link_0, link_1, ...)
            unique_tag = f"link_{idx}"
            
            # 고유 태그 정의 (기존 link 태그와 동일한 스타일)
            self.content_txt.tag_configure(
                unique_tag,
                foreground="blue",
                underline=True
            )
            # 우선순위 설정 (기존과 동일)
            self.content_txt.tag_lower("highlight", unique_tag)
            self.content_txt.tag_lower(unique_tag, "sel")
            
            # URL이 텍스트 내에 있는 모든 위치 찾기
            start_idx = "1.0"
            while True:
                # 다음 URL 위치 찾기
                pos = self.content_txt.search(url, start_idx, stopindex=tk.END, nocase=1)
                if not pos:
                    break
                
                # URL 끝 위치 계산
                end_idx = f"{pos}+{len(url)}c"
                
                # 고유 링크 태그
                self.content_txt.tag_add(unique_tag, pos, end_idx)
                
                # 싱글클릭 바인딩
                # self.content_txt.tag_bind(unique_tag, "<Button-1>", lambda e, u=url: self.open_link(u))
                
                # 다음 검색 시작 위치 업데이트
                start_idx = end_idx
        
        # SQL 태그 우선순위 복구
        self.content_txt.tag_lower("sql_keyword", "link")
        self.content_txt.tag_lower("link", "sel")

    def on_content_click(self, event):
        idx = self.content_txt.index(f"@{event.x},{event.y}")
        tags = self.content_txt.tag_names(idx)
        link_tag = next((t for t in tags if t.startswith("link_")), None)
        if link_tag:
            return

        self.on_content_selection(event)

        if self.link_update_timer:
            self.root.after_cancel(self.link_update_timer)
        self.link_update_timer = self.root.after(300, self.update_links)

        if self.sql_update_timer:
            self.root.after_cancel(self.sql_update_timer)
        self.sql_update_timer = self.root.after(300, self.highlight_sql)
        
        # Record 강조
        if hasattr(self, 'record_update_timer') and self.record_update_timer:
            self.root.after_cancel(self.record_update_timer)
        self.record_update_timer = self.root.after(300, self.highlight_record_blocks)
        
        # CMD 강조
        if hasattr(self, 'cmd_update_timer') and self.cmd_update_timer:
            self.root.after_cancel(self.cmd_update_timer)
        self.cmd_update_timer = self.root.after(300, self.highlight_cmd_blocks)
        
        # XML 강조
        if hasattr(self, 'xml_update_timer') and self.xml_update_timer:
            self.root.after_cancel(self.xml_update_timer)
        self.xml_update_timer = self.root.after(300, self.highlight_xml_blocks)

        # 클릭 시 Markdown 렌더링 호출
        # self.schedule_markdown_highlight()

        # Catalog 트리 업데이트 (클릭 시)
        self.update_catalog_tree()

    def on_content_double_click(self, event):
        """더블클릭 시 링크 열기"""
        idx = self.content_txt.index(f"@{event.x},{event.y}")
        tags = self.content_txt.tag_names(idx)
        
        # 링크 태그 찾기
        link_tag = next((t for t in tags if t.startswith("link_")), None)
        if not link_tag:
            return  # 링크가 아니면 아무것도 하지 않음
        
        # 해당 위치의 텍스트에서 URL 추출
        # 1. 링크 태그의 범위 가져오기
        ranges = self.content_txt.tag_ranges(link_tag)
        if not ranges:
            return
        
        # 2. 첫 번째 매칭된 범위에서 URL 추출
        start_idx = ranges[0]
        end_idx = ranges[1]
        url = self.content_txt.get(start_idx, end_idx)
        
        # 3. URL 열기
        self.open_link(url)
        
        # 4. 더블클릭으로 인한 선택 방지
        return "break"

    def on_content_motion(self, event):
        """마우스 이동 시 링크 위에 있으면 커서 변경"""
        # 마우스 위치의 인덱스 가져오기
        idx = self.content_txt.index(f"@{event.x},{event.y}")
        
        # 링크 태그 확인 (link_로 시작하는 모든 태그를 인식)
        tags = self.content_txt.tag_names(idx)
        is_link = any(t.startswith("link_") for t in tags)
        
        if is_link:
            self.content_txt.config(cursor="hand2")  # 손가락 커서
        else:
            self.content_txt.config(cursor="xterm")   # 일반 텍스트 커서

    def open_link(self, url):
        """링크 클릭 시 브라우저로 열기 (프로토콜 자동 추가)"""
        # URL에 프로토콜이 없는 경우 자동 추가 (서브도메인 지원 강화)
        if not url.startswith(('http://', 'https://', 'ftp://')):
            # volvo.net 계열 도메인은 https로 추가
            if any(domain in url for domain in ['volvo.net', 'codebeamer']):
                url = f"https://{url}"
            elif url.startswith('www.'):
                url = f"https://{url}"
            else:
                url = f"https://{url}"
        
        try:
            webbrowser.open(url)
        except Exception as e:
            messagebox.showerror("오류", f"링크를 열 수 없습니다: {str(e)}")

    def schedule_link_update(self):
        """링크 업데이트를 예약 (성능 최적화)"""
        if self.link_update_timer:
            self.root.after_cancel(self.link_update_timer)
        self.link_update_timer = self.root.after(500, self.update_links)

    def highlight_sql(self):
        """```sql ~ ``` 블록 내의 SQL 구문만 색상으로 강조 (문자열 강조 제거 버전)"""
        # 기존 SQL 태그 제거
        for tag in ["sql_keyword", "sql_string", "sql_comment", "sql_identifier"]:
            self.content_txt.tag_remove(tag, "1.0", tk.END)

        # 전체 텍스트 가져오기 (end-1c로 마지막 \n 제외)
        full_text = self.content_txt.get("1.0", "end-1c")
        if not full_text:
            return

        # SQL 코드 블록 패턴 (```sql ~ ```)
        sql_block_pattern = r'```sql\s*(.*?)\s*```'
        matches = re.finditer(sql_block_pattern, full_text, re.DOTALL | re.IGNORECASE)

        for match in matches:
            # SQL 블록의 전체 범위 먼저 정의
            block_start = match.start()
            block_end = match.end()
            
            # SQL 코드만 추출 (```sql과 ``` 사이의 내용)
            sql_content = match.group(1)
            
            # SQL 내용 시작 위치 (```sql 뒤의 공백까지 건너뛰기)
            sql_header = "```sql"
            sql_start = block_start + len(sql_header)
            while sql_start < block_end and sql_start < len(full_text) and full_text[sql_start].isspace():
                sql_start += 1
            
            # 1. SQL 주석 강조 (--로 시작하는 한 줄 주석)
            comment_pattern = r'--.*?$'
            for comment_match in re.finditer(comment_pattern, sql_content, re.MULTILINE):
                start_pos = sql_start + comment_match.start()
                end_pos = sql_start + comment_match.end()
                start_idx = self.absolute_to_text_index(start_pos)
                end_idx = self.absolute_to_text_index(end_pos)
                self.content_txt.tag_add("sql_comment", start_idx, end_idx)
            
            # 3. SQL 키워드 강조 (대소문자 무시)
            sql_keywords = [
                'SELECT', 'FROM', 'WHERE', 'INSERT', 'UPDATE', 'DELETE', 'JOIN', 'LEFT', 'RIGHT', 
                'INNER', 'OUTER', 'ON', 'AND', 'OR', 'NOT', 'IN', 'LIKE', 'GROUP', 'BY', 'HAVING',
                'ORDER', 'ASC', 'DESC', 'LIMIT', 'OFFSET', 'CREATE', 'TABLE', 'ALTER', 'DROP',
                'INSERT INTO', 'VALUES', 'SET', 'DISTINCT', 'COUNT', 'SUM', 'AVG', 'MAX', 'MIN',
                'AS', 'CASE', 'WHEN', 'THEN', 'ELSE', 'END', 'NULL', 'IS', 'BETWEEN', 'EXISTS'
            ]
            
            for keyword in sql_keywords:
                if ' ' in keyword:
                    pattern = r'\b' + re.escape(keyword) + r'\b'
                else:
                    pattern = r'\b' + keyword + r'\b'
                
                for keyword_match in re.finditer(pattern, sql_content, re.IGNORECASE):
                    start_pos = sql_start + keyword_match.start()
                    end_pos = sql_start + keyword_match.end()
                    
                    start_idx = self.absolute_to_text_index(start_pos)
                    end_idx = self.absolute_to_text_index(end_pos)
                    
                    if not self.is_in_tag(start_idx, ["sql_string", "sql_comment"]):
                        self.content_txt.tag_add("sql_keyword", start_idx, end_idx)
            
            # 4. SQL 식별자 강조 (테이블/컬럼명)
            identifier_patterns = [
                r'(?<=FROM\s)\w+', r'(?<=JOIN\s)\w+', r'(?<=UPDATE\s)\w+',
                r'(?<=INSERT INTO\s)\w+', r'(?<=CREATE TABLE\s)\w+'
            ]
            
            for pattern in identifier_patterns:
                for id_match in re.finditer(pattern, sql_content, re.IGNORECASE):
                    start_pos = sql_start + id_match.start()
                    end_pos = sql_start + id_match.end()
                    
                    start_idx = self.absolute_to_text_index(start_pos)
                    end_idx = self.absolute_to_text_index(end_pos)
                    
                    if not self.is_in_tag(start_idx, ["sql_string", "sql_comment"]):
                        self.content_txt.tag_add("sql_identifier", start_idx, end_idx)

    def highlight_record_blocks(self):
        """```record 또는 ```log 블록 내의 텍스트를 Consolas 폰트로 표시"""
        # 기존 record_block 태그 제거
        self.content_txt.tag_remove("record_block", "1.0", tk.END)

        # 전체 텍스트 가져오기 (end-1c로 마지막 \n 제외)
        full_text = self.content_txt.get("1.0", "end-1c")
        if not full_text:
            return

        # 정규식 패턴 : record 또는 log 블록 인식
        record_block_pattern = r'```(record|log)\s*(.*?)\s*```'
        matches = re.finditer(record_block_pattern, full_text, re.DOTALL | re.IGNORECASE)

        for match in matches:
            # Record/Log 블록의 전체 범위 정의
            block_start = match.start()
            block_end = match.end()
            
            # 블록 헤더 (record/log) 길이 계산
            block_type = match.group(1)  # record 또는 log
            record_header = f"```{block_type}"
            record_start = block_start + len(record_header)
            
            # 헤더 뒤의 공백 건너뛰기
            while record_start < block_end and record_start < len(full_text) and full_text[record_start].isspace():
                record_start += 1
            
            # 블록 푸터 (```) 앞의 공백 건너뛰기
            record_footer = "```"
            record_end = block_end - len(record_footer)
            while record_end > record_start and full_text[record_end-1].isspace():
                record_end -= 1
            
            # Record/Log 블록 내 텍스트에 태그 적용
            if record_start < record_end:
                start_idx = self.absolute_to_text_index(record_start)
                end_idx = self.absolute_to_text_index(record_end)
                self.content_txt.tag_add("record_block", start_idx, end_idx)

    def highlight_cmd_blocks(self):
        """CMD 블록 내 실제 내용만 정확히 검은 배경 적용 (빈 줄/공백 완전 제외)"""
        # 기존 태그 전체 제거
        self.content_txt.tag_remove("cmd_block", "1.0", tk.END)
        
        # 텍스트를 라인별로 분리하여 처리 (가장 정확한 방식)
        all_lines = self.content_txt.get("1.0", tk.END).split("\n")
        in_cmd_block = False
        cmd_block_start_line = 0
        cmd_block_type = None

        # 라인별로 CMD 블록 시작/끝 검사
        for line_idx, line_content in enumerate(all_lines):
            # 1. CMD 블록 시작 (```cmd/command/terminal)
            if not in_cmd_block and line_content.strip().startswith("```"):
                block_type = line_content.strip()[3:].lower()
                if block_type in ["cmd", "command", "terminal"]:
                    in_cmd_block = True
                    cmd_block_start_line = line_idx + 1  # tkinter는 1-based 라인 번호
                    cmd_block_type = block_type
                    continue
            
            # 2. CMD 블록 끝 (```)
            if in_cmd_block and line_content.strip() == "```":
                in_cmd_block = False
                continue
            
            # 3. CMD 블록 내 실제 내용 처리 (빈 줄 제외)
            if in_cmd_block:
                # 빈 줄은 처리하지 않음 (공백만 있는 줄도 제외)
                if not line_content.strip():
                    continue
                
                # 정확한 라인/컬럼 인덱스 계산 (tkinter 표준 방식)
                line_num = line_idx + 1  # tkinter 라인 번호는 1부터 시작
                start_idx = f"{line_num}.0"          # 라인 시작
                end_idx = f"{line_num}.{len(line_content)}"  # 라인 끝 (실제 내용 길이만큼)
                
                # 태그 적용
                self.content_txt.tag_add("cmd_block", start_idx, end_idx)

        # 태그 스타일 유지 (기존 설정 그대로)
        self.content_txt.tag_configure(
            "cmd_block",
            font=("Consolas", 11),
            background="black",
            foreground="#E0E0E0"
        )
                
    def highlight_xml_blocks(self):
        """```xml 블록 내의 텍스트를 XML 스타일로 강조"""
        # 기존 xml_block 태그 제거
        self.content_txt.tag_remove("xml_block", "1.0", tk.END)
        self.content_txt.tag_remove("xml_tag", "1.0", tk.END)
        self.content_txt.tag_remove("xml_attr", "1.0", tk.END)
        self.content_txt.tag_remove("xml_value", "1.0", tk.END)
        self.content_txt.tag_remove("xml_comment", "1.0", tk.END)

        # 전체 텍스트 가져오기 (end-1c로 마지막 \n 제외)
        full_text = self.content_txt.get("1.0", "end-1c")
        if not full_text:
            return

        # XML 코드 블록 패턴 (```xml ~ ```)
        xml_block_pattern = r'```xml\s*(.*?)\s*```'
        matches = re.finditer(xml_block_pattern, full_text, re.DOTALL | re.IGNORECASE)

        # XML 태그 스타일 정의
        self.content_txt.tag_configure("xml_block", font=("Consolas", 11), background="#f8f8f8")
        self.content_txt.tag_configure("xml_tag", foreground="#800080", font=("Consolas", 11, "bold"))  # 보라색 태그
        self.content_txt.tag_configure("xml_attr", foreground="#ff4500", font=("Consolas", 11))        # 주황색 속성명
        self.content_txt.tag_configure("xml_value", foreground="#008000", font=("Consolas", 11))       # 초록색 속성값
        self.content_txt.tag_configure("xml_comment", foreground="#808080", font=("Consolas", 11, "italic"))  # 회색 주석

        for match in matches:
            # XML 블록의 전체 범위 정의
            block_start = match.start()
            block_end = match.end()
            
            # XML 코드만 추출 (```xml과 ``` 사이의 내용)
            xml_content = match.group(1)
            
            # XML 내용 시작 위치 (```xml 뒤의 공백까지 건너뛰기)
            xml_header = "```xml"
            xml_start = block_start + len(xml_header)
            while xml_start < block_end and xml_start < len(full_text) and full_text[xml_start].isspace():
                xml_start += 1
            
            # 1. XML 블록 전체 배경 적용
            start_idx = self.absolute_to_text_index(xml_start)
            end_idx = self.absolute_to_text_index(block_end - 3)  # ``` 앞까지
            self.content_txt.tag_add("xml_block", start_idx, end_idx)

            # 2. XML 주석 강조 (<!-- ~ -->)
            comment_pattern = r'<!--.*?-->'
            for comment_match in re.finditer(comment_pattern, xml_content, re.DOTALL):
                start_pos = xml_start + comment_match.start()
                end_pos = xml_start + comment_match.end()
                start_idx = self.absolute_to_text_index(start_pos)
                end_idx = self.absolute_to_text_index(end_pos)
                self.content_txt.tag_add("xml_comment", start_idx, end_idx)

            # 3. XML 태그 강조 (<태그>, </태그>, <태그/>)
            tag_pattern = r'</?\w+[^>]*\/?>'
            for tag_match in re.finditer(tag_pattern, xml_content):
                start_pos = xml_start + tag_match.start()
                end_pos = xml_start + tag_match.end()
                tag_text = tag_match.group()
                
                # 태그 이름 추출 (예: <root> → root)
                tag_name_match = re.search(r'</?(\w+)', tag_text)
                if tag_name_match:
                    tag_name = tag_name_match.group(1)
                    tag_name_start = start_pos + tag_name_match.start(1)
                    tag_name_end = tag_name_start + len(tag_name)
                    
                    # 태그 이름 강조
                    start_idx = self.absolute_to_text_index(tag_name_start)
                    end_idx = self.absolute_to_text_index(tag_name_end)
                    self.content_txt.tag_add("xml_tag", start_idx, end_idx)

                # 4. 속성명과 속성값 강조
                attr_pattern = r'(\w+)\s*=\s*["\'](.*?)["\']'
                for attr_match in re.finditer(attr_pattern, tag_text):
                    # 속성명 강조
                    attr_name_start = start_pos + attr_match.start(1)
                    attr_name_end = start_pos + attr_match.end(1)
                    start_idx = self.absolute_to_text_index(attr_name_start)
                    end_idx = self.absolute_to_text_index(attr_name_end)
                    self.content_txt.tag_add("xml_attr", start_idx, end_idx)
                    
                    # 속성값 강조
                    attr_val_start = start_pos + attr_match.start(2)
                    attr_val_end = start_pos + attr_match.end(2)
                    start_idx = self.absolute_to_text_index(attr_val_start)
                    end_idx = self.absolute_to_text_index(attr_val_end)
                    self.content_txt.tag_add("xml_value", start_idx, end_idx)

        # 태그 우선순위 설정 (선택 태그보다 아래)
        self.content_txt.tag_lower("xml_block", "sel")
        self.content_txt.tag_lower("xml_tag", "sel")
        self.content_txt.tag_lower("xml_attr", "sel")
        self.content_txt.tag_lower("xml_value", "sel")
        self.content_txt.tag_lower("xml_comment", "sel")

    def highlight_markdown_headers(self):
        """Markdown 제목 (#, ##, ### 등) 스타일 적용 - 노트 전환/오픈 시에만 실행"""
        # 기존 Markdown 제목 태그 제거
        for tag in ["md_h1", "md_h2", "md_h3", "md_h4", "md_h5", "md_h6"]:
            self.content_txt.tag_remove(tag, "1.0", tk.END)

        # Markdown 제목 태그 재정의
        self.content_txt.tag_configure("md_h1", font=("맑은 고딕", 22, "bold"), foreground="#2c3e50")
        self.content_txt.tag_configure("md_h2", font=("맑은 고딕", 20, "bold"), foreground="#34495e")
        self.content_txt.tag_configure("md_h3", font=("맑은 고딕", 18, "bold"), foreground="#2d3436")
        self.content_txt.tag_configure("md_h4", font=("맑은 고딕", 16, "bold"), foreground="#636e72")
        self.content_txt.tag_configure("md_h5", font=("맑은 고딕", 14, "bold"), foreground="#636e72")
        self.content_txt.tag_configure("md_h6", font=("맑은 고딕", 12, "bold"), foreground="#636e72")

        # 전체 텍스트를 라인별로 처리
        all_lines = self.content_txt.get("1.0", tk.END).split("\n")
        
        for line_idx, line_content in enumerate(all_lines):
            stripped_line = line_content.strip()
            
            # 코드 블록 내에서는 Markdown 제목 처리하지 않음
            if stripped_line.startswith("```"):
                continue
            
            # Markdown 제목 패턴 확인
            if stripped_line.startswith("###### "):  # h6
                header_level = 6
            elif stripped_line.startswith("##### "):  # h5
                header_level = 5
            elif stripped_line.startswith("#### "):   # h4
                header_level = 4
            elif stripped_line.startswith("### "):    # h3
                header_level = 3
            elif stripped_line.startswith("## "):     # h2
                header_level = 2
            elif stripped_line.startswith("# "):      # h1
                header_level = 1
            else:
                continue  # 제목이 아니면 건너뛰기
            
            # 라인 번호 계산 (tkinter는 1-based)
            line_num = line_idx + 1
            
            # 제목 기호(#) 포함 전체 라인에 태그 적용
            start_idx = f"{line_num}.0"
            end_idx = f"{line_num}.{len(line_content)}"
            
            # 해당 레벨의 태그 적용
            tag_name = f"md_h{header_level}"
            self.content_txt.tag_add(tag_name, start_idx, end_idx)
        
        # 선택 태그가 항상 위에 오도록 설정
        self.content_txt.tag_raise("sel", "md_h1")
        self.content_txt.tag_raise("sel", "md_h2")
        self.content_txt.tag_raise("sel", "md_h3")
        self.content_txt.tag_raise("sel", "md_h4")
        self.content_txt.tag_raise("sel", "md_h5")
        self.content_txt.tag_raise("sel", "md_h6")

    def is_in_tag(self, pos, tags_to_check):
        """주어진 위치가 특정 태그 영역 내에 있는지 확인"""
        try:
            for tag in tags_to_check:
                ranges = self.content_txt.tag_ranges(tag)
                for i in range(0, len(ranges), 2):
                    start = ranges[i]
                    end = ranges[i+1]
                    if self.content_txt.compare(pos, ">=", start) and self.content_txt.compare(pos, "<=", end):
                        return True
            return False
        except:
            return False

    def schedule_sql_highlight(self):
        """SQL 강조 업데이트 예약 (성능 최적화)"""
        if self.sql_update_timer:
            self.root.after_cancel(self.sql_update_timer)
        self.sql_update_timer = self.root.after(500, self.highlight_sql)

    def schedule_record_highlight(self):
        """Record 블록 강조 업데이트 예약 (성능 최적화)"""
        # Record 업데이트 타이머 변수 초기화 (create_ui에서 선언 필요)
        if not hasattr(self, 'record_update_timer'):
            self.record_update_timer = None
        
        if self.record_update_timer:
            self.root.after_cancel(self.record_update_timer)
        self.record_update_timer = self.root.after(500, self.highlight_record_blocks)

    def schedule_cmd_highlight(self):
        """CMD 블록 강조 업데이트 예약 (성능 최적화 + 실시간 반영)"""
        # CMD 업데이트 타이머 변수 초기화
        if not hasattr(self, 'cmd_update_timer'):
            self.cmd_update_timer = None
        
        if self.cmd_update_timer:
            self.root.after_cancel(self.cmd_update_timer)
        # 실시간 반영
        self.cmd_update_timer = self.root.after(500, self.highlight_cmd_blocks)

    def schedule_xml_highlight(self):
        """XML 강조 업데이트 예약 (성능 최적화 + 실시간 반영)"""
        if not hasattr(self, 'xml_update_timer'):
            self.xml_update_timer = None
        
        if self.xml_update_timer:
            self.root.after_cancel(self.xml_update_timer)
        # 실시간 반영
        self.xml_update_timer = self.root.after(500, self.highlight_xml_blocks)

    def schedule_markdown_highlight(self):
        """Markdown 제목 강조 업데이트 예약 (성능 최적화)"""
        if not hasattr(self, 'markdown_update_timer'):
            self.markdown_update_timer = None
        
        if self.markdown_update_timer:
            self.root.after_cancel(self.markdown_update_timer)
        self.markdown_update_timer = self.root.after(500, self.highlight_markdown_headers)

    def parse_markdown_headers(self):
        """내용 영역에서 Markdown 헤더를 파싱하여 catalog 데이터로 변환"""
        self.markdown_headers = []
        
        # 내용 텍스트가 없으면 빈 리스트 반환
        if not hasattr(self, 'content_txt'):
            return
            
        all_lines = self.content_txt.get("1.0", tk.END).split("\n")
        
        # 코드 블록 내부 여부를 추적하는 플래그
        in_code_block = False
        
        for line_idx, line_content in enumerate(all_lines):
            stripped_line = line_content.strip()
            
            # 코드 블록 시작/끝 감지
            if stripped_line.startswith("```"):
                in_code_block = not in_code_block
                continue  # 코드 블록 라인 자체는 헤더로 처리하지 않음
            
            # 코드 블록 내부이면 헤더 파싱 건너뛰기
            if in_code_block:
                continue
            
            # Markdown 헤더 레벨 확인
            header_level = 0
            header_text = ""
            header_start = ""
            
            # 헤더 기호 개수로 레벨 판단 (정확한 공백 체크)
            if stripped_line.startswith("###### ") and len(stripped_line) > 7:
                header_level = 6
                header_text = stripped_line[7:].strip()
            elif stripped_line.startswith("##### ") and len(stripped_line) > 6:
                header_level = 5
                header_text = stripped_line[6:].strip()
            elif stripped_line.startswith("#### ") and len(stripped_line) > 5:
                header_level = 4
                header_text = stripped_line[5:].strip()
            elif stripped_line.startswith("### ") and len(stripped_line) > 4:
                header_level = 3
                header_text = stripped_line[4:].strip()
            elif stripped_line.startswith("## ") and len(stripped_line) > 3:
                header_level = 2
                header_text = stripped_line[3:].strip()
            elif stripped_line.startswith("# ") and len(stripped_line) > 2:
                header_level = 1
                header_text = stripped_line[2:].strip()
            
            # 헤더 텍스트가 유효한 경우에만 추가
            if header_level > 0 and header_text and len(header_text) > 0:
                # 헤더 시작 위치 (tkinter 인덱스 형식)
                line_num = line_idx + 1
                header_start = f"{line_num}.0"
                
                self.markdown_headers.append({
                    "text": header_text,
                    "start": header_start,
                    "level": header_level
                })

    def update_catalog_tree(self):
        """Catalog 트리를 업데이트 (실제 문서 순서대로 표시)"""
        
        # catalog_tree가 초기화되지 않았으면 실행하지 않음
        if self.catalog_tree is None:
            return
        
        # 기존 트리 아이템 삭제 (모든 아이템 제거)
        try:
            for item in self.catalog_tree.get_children():
                self.catalog_tree.delete(item)
        except:
            pass
        
        # 현재 선택된 노트가 없으면 종료
        if self.current_id is None:
            return
        
        # 헤더 파싱
        self.parse_markdown_headers()
        
        # 트리에 헤더 추가 (실제 문서 순서대로 + 레벨에 따른 계층 구조)
        parent_stack = []  # 부모 아이템을 관리할 스택 (레벨 순서 유지)
        
        for header in self.markdown_headers:
            try:
                level = header["level"]
                text = header["text"]
                start_pos = header["start"]
                
                # 스택을 사용하여 실제 문서 순서대로 부모를 관리
                # 현재 레벨보다 높은 레벨의 부모는 스택에서 제거
                while parent_stack and parent_stack[-1]["level"] >= level:
                    parent_stack.pop()
                
                # 부모 아이템 결정 (스택의 마지막 아이템이 현재 레벨의 직계 부모)
                parent_id = ""
                if parent_stack:
                    parent_id = parent_stack[-1]["item_id"]
                
                # 트리 아이템 추가 (실제 문서 순서대로 end 위치에 추가)
                item_id = self.catalog_tree.insert(
                    parent_id,
                    "end",  # 항상 마지막 위치에 추가하여 문서 순서 유지
                    text=text,
                    values=(start_pos,)  # 위치 정보 저장
                )
                
                # 항목 생성 시 즉시 펼치기
                self.catalog_tree.item(item_id, open=True)
                
                # 현재 헤더를 스택에 추가 (다음 헤더의 부모로 사용될 수 있음)
                parent_stack.append({
                    "level": level,
                    "item_id": item_id
                })
                
                # 레벨별 스타일 설정
                if level == 1:
                    self.catalog_tree.item(item_id, tags=("h1",))
                elif level == 2:
                    self.catalog_tree.item(item_id, tags=("h2",))
                elif level == 3:
                    self.catalog_tree.item(item_id, tags=("h3",))
                else:
                    self.catalog_tree.item(item_id, tags=("h4+",))
            except Exception as e:
                # 오류 발생 시 계속 진행
                continue
        
        # 트리 태그 스타일 설정
        self.catalog_tree.tag_configure("h1", font=("맑은 고딕", 10, "bold"), foreground="#2c3e50")
        self.catalog_tree.tag_configure("h2", font=("맑은 고딕", 9, "bold"), foreground="#34495e")
        self.catalog_tree.tag_configure("h3", font=("맑은 고딕", 9), foreground="#7f8c8d")
        self.catalog_tree.tag_configure("h4+", font=("맑은 고딕", 8), foreground="#95a5a6")
        
        # UI 업데이트
        self.catalog_tree.update_idletasks()
        
    def on_catalog_select(self, event):
        """Catalog 트리 아이템 클릭 시 해당 섹션으로 이동 (밑줄 제거)"""
        selected_items = self.catalog_tree.selection()
        if not selected_items:
            return
        
        item_id = selected_items[0]
        start_pos = self.catalog_tree.item(item_id, "values")[0]
        
        # 해당 위치로 스크롤하고 포커스 이동
        self.content_txt.see(start_pos)
        self.content_txt.mark_set(tk.INSERT, start_pos)
        self.content_txt.focus_set()
        
        # 선택된 위치 하이라이트 (밑줄 제거)
        self.content_txt.tag_remove("catalog_highlight", "1.0", tk.END)
        self.content_txt.tag_configure(
            "catalog_highlight",
            background="#e6f7ff",
            underline=False  # 밑줄 제거
        )
        
        # 해당 라인 전체 하이라이트
        line_num = start_pos.split(".")[0]
        self.content_txt.tag_add(
            "catalog_highlight",
            f"{line_num}.0",
            f"{line_num}.end"
        )

    # 기존 toggle_markdown_header 메서드는 그대로 유지하되, 마지막에 반드시 "break" 반환
    def toggle_markdown_header(self, level, event=None):
        """선택된 모든 라인에 Markdown 제목 기호를 토글 (추가/제거) - 완전 개선 버전"""
        # content_txt에 포커스 적용
        self.content_txt.focus_set()
        
        try:
            # 선택 영역 확인 (여러 줄 선택 지원)
            start_line = None
            end_line = None
            
            if self.content_txt.tag_ranges("sel"):
                # 선택 영역의 시작과 끝 라인 가져오기
                sel_start = self.content_txt.index(tk.SEL_FIRST)
                sel_end = self.content_txt.index(tk.SEL_LAST)
                start_line = int(sel_start.split(".")[0])
                end_line = int(sel_end.split(".")[0])
            else:
                # 커서 위치의 단일 라인
                insert_pos = self.content_txt.index(tk.INSERT)
                start_line = int(insert_pos.split(".")[0])
                end_line = start_line
            
            # 해당 레벨의 제목 기호
            header_symbol = "#" * level
            header_with_space = f"{header_symbol} "
            
            # undo 포인트 생성
            self.content_txt.edit_separator()
            
            # 선택된 모든 라인에 대해 처리
            for line_num in range(start_line, end_line + 1):
                line_start_idx = f"{line_num}.0"
                line_end_idx = f"{line_num}.end"
                
                # 현재 라인의 원본 텍스트 가져오기 (공백 유지)
                original_line = self.content_txt.get(line_start_idx, line_end_idx)
                # 앞쪽 공백을 제외한 텍스트
                stripped_line = original_line.lstrip()
                
                # 앞쪽 공백 계산
                leading_spaces = len(original_line) - len(stripped_line)
                
                # 제목 기호 토글 로직
                if stripped_line.startswith(header_with_space):
                    # 같은 레벨의 제목 기호 제거
                    new_text = original_line[:leading_spaces] + stripped_line[len(header_with_space):]
                elif stripped_line.startswith("#"):
                    # 다른 레벨의 제목 기호가 있는 경우: 기존 제거 후 새로운 레벨 추가
                    # 기존 제목 기호 길이 계산
                    existing_header_len = 0
                    for char in stripped_line:
                        if char == "#":
                            existing_header_len += 1
                        else:
                            break
                    # 기존 제목 기호 + 공백 제거
                    if existing_header_len > 0 and len(stripped_line) > existing_header_len and stripped_line[existing_header_len] == " ":
                        new_stripped = stripped_line[existing_header_len + 1:]
                    else:
                        new_stripped = stripped_line[existing_header_len:]
                    # 새로운 레벨의 제목 기호 추가
                    new_text = original_line[:leading_spaces] + header_with_space + new_stripped
                else:
                    # 제목 기호가 없는 경우: 새로운 레벨 추가
                    new_text = original_line[:leading_spaces] + header_with_space + stripped_line
                
                # 라인 텍스트 업데이트
                self.content_txt.delete(line_start_idx, line_end_idx)
                self.content_txt.insert(line_start_idx, new_text)
            
            # undo 포인트 생성
            self.content_txt.edit_separator()
            
            # 커서 위치 유지 (마지막 처리 라인의 끝으로 이동)
            last_line_len = len(self.content_txt.get(f"{end_line}.0", f"{end_line}.end"))
            cursor_pos = f"{end_line}.{last_line_len}"
            self.content_txt.mark_set(tk.INSERT, cursor_pos)
            self.content_txt.see(cursor_pos)
            
            # Catalog 트리 (지연 실행)
            self.root.after(100, self.update_catalog_tree)
            
            # Markdown 헤더 강조
            self.highlight_markdown_headers()
            
        except Exception as e:
            print(f"Markdown 제목 토글 오류: {e}")
        
        # 이벤트 전파 완전 차단
        return "break"

if __name__ == "__main__":
    root = tk.Tk()
    NoteApp(root)
    root.mainloop()