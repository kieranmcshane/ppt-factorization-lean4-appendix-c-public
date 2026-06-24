import AppKit
import Foundation

struct ChecklistItem: Codable {
    let label: String
    let checked: Bool
    let evidence: String
}

struct ChecklistSection: Codable {
    let name: String
    let items: [ChecklistItem]
}

struct ChecklistState: Codable {
    let title: String
    let subtitle: String
    let updated: String
    let completed: Int
    let total: Int
    let sections: [ChecklistSection]
    let openItems: [String]
}

final class ChecklistStore {
    let url: URL
    let generatorURL: URL?
    private(set) var state: ChecklistState

    init(url: URL) {
        self.url = url
        let candidate = url.deletingLastPathComponent().appendingPathComponent("generate_appendix_b_progress.py")
        self.generatorURL = FileManager.default.fileExists(atPath: candidate.path) ? candidate : nil
        self.state = ChecklistStore.load(url: url) ?? ChecklistStore.fallback
        reload()
    }

    func reload() {
        runGeneratorIfPresent()
        if let next = ChecklistStore.load(url: url) {
            state = next
        }
    }

    private func runGeneratorIfPresent() {
        guard let generatorURL else { return }
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/env")
        process.arguments = ["python3", generatorURL.path, url.path]
        process.currentDirectoryURL = generatorURL.deletingLastPathComponent().deletingLastPathComponent()
        try? process.run()
        process.waitUntilExit()
    }

    private static func load(url: URL) -> ChecklistState? {
        guard let data = try? Data(contentsOf: url) else { return nil }
        return try? JSONDecoder().decode(ChecklistState.self, from: data)
    }

    private static let fallback = ChecklistState(
        title: "Appendix B Checklist",
        subtitle: "Waiting for repo facts",
        updated: "",
        completed: 0,
        total: 0,
        sections: [],
        openItems: ["Create or regenerate tools/appendix_b_progress.json"]
    )
}

final class ChecklistView: NSView {
    var store: ChecklistStore

    private let bg = NSColor(calibratedRed: 0.055, green: 0.075, blue: 0.10, alpha: 0.97)
    private let panel = NSColor(calibratedRed: 0.095, green: 0.12, blue: 0.155, alpha: 1)
    private let text = NSColor(calibratedRed: 0.92, green: 0.95, blue: 0.95, alpha: 1)
    private let muted = NSColor(calibratedRed: 0.62, green: 0.68, blue: 0.70, alpha: 1)
    private let green = NSColor(calibratedRed: 0.25, green: 0.77, blue: 0.52, alpha: 1)
    private let amber = NSColor(calibratedRed: 0.96, green: 0.68, blue: 0.22, alpha: 1)
    private let red = NSColor(calibratedRed: 0.95, green: 0.35, blue: 0.34, alpha: 1)

    private let titleLabel = NSTextField(labelWithString: "")
    private let subtitleLabel = NSTextField(labelWithString: "")
    private let updatedLabel = NSTextField(labelWithString: "")
    private let summaryLabel = NSTextField(labelWithString: "")
    private let openLabel = NSTextField(labelWithString: "")
    private let copyButton = NSButton(title: "Copy All", target: nil, action: nil)
    private let scrollView = NSScrollView()
    private let textView = NSTextView()

    init(frame: NSRect, store: ChecklistStore) {
        self.store = store
        super.init(frame: frame)
        wantsLayer = true
        layer?.backgroundColor = bg.cgColor
        layer?.masksToBounds = true
        configure()
        needsLayout = true
        layoutSubtreeIfNeeded()
        refresh()
    }

    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    override var isFlipped: Bool { true }

    override func setFrameSize(_ newSize: NSSize) {
        super.setFrameSize(newSize)
        needsLayout = true
    }

    override func layout() {
        super.layout()
        let margin: CGFloat = 24
        let width = bounds.width - 2 * margin
        let titleHeight: CGFloat = 34
        let subtitleHeight: CGFloat = 18
        let summaryHeight: CGFloat = 24
        let buttonWidth: CGFloat = 82

        titleLabel.frame = NSRect(x: margin, y: 18, width: width - buttonWidth - 16, height: titleHeight)
        updatedLabel.frame = NSRect(x: bounds.width - margin - 180, y: 22, width: 180, height: 16)
        copyButton.frame = NSRect(x: bounds.width - margin - buttonWidth, y: 50, width: buttonWidth, height: 26)
        subtitleLabel.frame = NSRect(x: margin, y: 54, width: width - buttonWidth - 20, height: subtitleHeight)
        summaryLabel.frame = NSRect(x: margin, y: 78, width: width, height: summaryHeight)
        openLabel.frame = NSRect(x: margin, y: 104, width: width, height: summaryHeight)

        let scrollY: CGFloat = 136
        scrollView.frame = NSRect(x: margin, y: scrollY, width: width, height: max(120, bounds.height - scrollY - margin))
        updateTextDocumentSize()
    }

    func refresh() {
        let state = store.state
        titleLabel.attributedStringValue = ChecklistView.styled(state.title, font: .systemFont(ofSize: 24, weight: .bold), color: text)
        subtitleLabel.attributedStringValue = ChecklistView.styled(state.subtitle, font: .systemFont(ofSize: 12, weight: .medium), color: muted)
        updatedLabel.attributedStringValue = ChecklistView.styled("Updated \(state.updated)", font: .systemFont(ofSize: 11, weight: .medium), color: muted, alignment: .right)

        let openCount = max(0, state.total - state.completed)
        let summaryColor: NSColor = openCount == 0 ? green : (openCount <= 2 ? amber : red)
        summaryLabel.attributedStringValue = ChecklistView.styled("\(state.completed) / \(state.total) objective criteria met", font: .systemFont(ofSize: 14, weight: .bold), color: summaryColor)
        openLabel.attributedStringValue = ChecklistView.styled("\(openCount) still open", font: .systemFont(ofSize: 12, weight: .bold), color: openCount == 0 ? green : red)
        textView.string = ChecklistView.renderText(state)
        updateTextDocumentSize()
    }

    @objc private func copyAll() {
        let pasteboard = NSPasteboard.general
        pasteboard.clearContents()
        pasteboard.setString(textView.string, forType: .string)
    }

    private func configure() {
        [titleLabel, subtitleLabel, updatedLabel, summaryLabel, openLabel].forEach {
            $0.isEditable = false
            $0.isBordered = false
            $0.isBezeled = false
            $0.drawsBackground = false
            $0.lineBreakMode = .byTruncatingTail
            $0.maximumNumberOfLines = 1
        }
        updatedLabel.alignment = .right
        openLabel.alignment = .left

        copyButton.target = self
        copyButton.action = #selector(copyAll)
        copyButton.bezelStyle = .rounded
        copyButton.controlSize = .small
        copyButton.font = .systemFont(ofSize: 11, weight: .semibold)
        copyButton.toolTip = "Copy the full checklist text"

        textView.isEditable = false
        textView.isSelectable = true
        textView.isRichText = false
        textView.drawsBackground = true
        textView.backgroundColor = panel
        textView.textColor = text
        textView.font = .monospacedSystemFont(ofSize: 12, weight: .regular)
        textView.textContainerInset = NSSize(width: 14, height: 14)
        textView.textContainer?.lineFragmentPadding = 0
        textView.isVerticallyResizable = true
        textView.isHorizontallyResizable = false
        textView.autoresizingMask = [.width]
        textView.textContainer?.widthTracksTextView = true
        textView.textContainer?.containerSize = NSSize(width: 1000, height: CGFloat.greatestFiniteMagnitude)

        scrollView.hasVerticalScroller = true
        scrollView.hasHorizontalScroller = false
        scrollView.drawsBackground = false
        scrollView.borderType = .noBorder
        scrollView.documentView = textView

        [titleLabel, subtitleLabel, updatedLabel, summaryLabel, openLabel, copyButton, scrollView].forEach {
            addSubview($0)
        }
    }

    private func updateTextDocumentSize() {
        let width = max(260, scrollView.contentSize.width)
        let string = textView.string as NSString
        let attributes: [NSAttributedString.Key: Any] = [
            .font: NSFont.monospacedSystemFont(ofSize: 12, weight: .regular)
        ]
        textView.textContainer?.containerSize = NSSize(width: width - 28, height: CGFloat.greatestFiniteMagnitude)
        let boundsRect = string.boundingRect(
            with: NSSize(width: width - 28, height: CGFloat.greatestFiniteMagnitude),
            options: [.usesLineFragmentOrigin, .usesFontLeading],
            attributes: attributes
        )
        let height = ceil(boundsRect.height) + 28
        textView.frame = NSRect(x: 0, y: 0, width: width, height: max(height, scrollView.contentSize.height))
    }

    private static func styled(
        _ value: String,
        font: NSFont,
        color: NSColor,
        alignment: NSTextAlignment = .left
    ) -> NSAttributedString {
        let paragraph = NSMutableParagraphStyle()
        paragraph.alignment = alignment
        paragraph.lineBreakMode = .byTruncatingTail
        return NSAttributedString(
            string: value,
            attributes: [
                .font: font,
                .foregroundColor: color,
                .paragraphStyle: paragraph
            ]
        )
    }

    private static func renderText(_ state: ChecklistState) -> String {
        var lines: [String] = []
        lines.append(state.title)
        lines.append(state.subtitle)
        lines.append("Updated \(state.updated)")
        lines.append("\(state.completed) / \(state.total) objective criteria met")
        lines.append("")

        for section in state.sections {
            let doneCount = section.items.filter(\.checked).count
            lines.append("\(section.name) (\(doneCount) / \(section.items.count))")
            for item in section.items {
                let mark = item.checked ? "☑" : "☐"
                lines.append("\(mark) \(item.label)")
                lines.append("  \(item.evidence)")
            }
            lines.append("")
        }

        if !state.openItems.isEmpty {
            lines.append("Open Now")
            for item in state.openItems {
                lines.append("• \(item)")
            }
        }

        return lines.joined(separator: "\n")
    }
}

final class AppDelegate: NSObject, NSApplicationDelegate {
    private var window: NSWindow!
    private var timer: Timer?
    private var view: ChecklistView!
    private var store: ChecklistStore!

    func applicationDidFinishLaunching(_ notification: Notification) {
        let bundledPath = Bundle.main.url(forResource: "appendix_b_progress", withExtension: "json")?.path
        let path = CommandLine.arguments.dropFirst().first ?? bundledPath ?? "tools/appendix_b_progress.json"
        let url = URL(fileURLWithPath: path)

        store = ChecklistStore(url: url)
        view = ChecklistView(frame: NSRect(x: 0, y: 0, width: 540, height: 860), store: store)
        view.autoresizingMask = [.width, .height]

        window = NSWindow(
            contentRect: NSRect(x: 120, y: 120, width: 540, height: 860),
            styleMask: [.titled, .closable, .miniaturizable, .resizable],
            backing: .buffered,
            defer: false
        )
        window.title = "Appendix B Checklist"
        window.contentView = view
        window.isReleasedWhenClosed = false
        window.level = .floating
        window.collectionBehavior = [.canJoinAllSpaces, .fullScreenAuxiliary]
        window.makeKeyAndOrderFront(nil)
        NSApp.activate(ignoringOtherApps: true)

        timer = Timer.scheduledTimer(withTimeInterval: 4.0, repeats: true) { [weak self] _ in
            self?.store.reload()
            self?.view.refresh()
        }
    }
}

let app = NSApplication.shared
let delegate = AppDelegate()
app.delegate = delegate
app.setActivationPolicy(.regular)
app.run()
