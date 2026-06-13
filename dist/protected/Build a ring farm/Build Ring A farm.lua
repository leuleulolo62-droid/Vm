-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'AsIjxiVzPLL4SjXj94PQSXiY'
local __p = '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Ow82SltdPjUCLQw8LzEsD1BAdh8+KGxRPQ5SDExaMyU6Nwd5AAY9BT0fMxQkP2JHNh4ZBlBRPgQVF0EvaFNpSjkcIhUVOilaJxl2OU1VJDR9OQUwJB0cLDdJa1omd2wUcwM+Sk8UJDk2Nkk7KB0tKxQAMxR4ZWxRPQ54D1dQWjcmNgotKBwnSjkcIhUVOilaJxl2GVxAGjQgLAwrAxw6GVAff1oROThbFhw9BE1HfgInOR08bxksGQwMJDg/Pz8UbkouURldNnEleB0xJB1pCBEHMjA1PzhRIUJxSlxaNHE2Ng1TJwYnCQwAORRwDTlAPC8uD1dAI38gKAA3Dxw+QlFJBB89IzhRIEQxBE9bOzR7ejs8MAYsGQw6JhM+bmAUNQs0GVwdcDQ9PGNTbF5piO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35XFd9bH0EfUoZP217cAEWDDpTbF5piO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35XBY/Ly1YcystHlZkNSUgeFR5OlMaHhkdM1ptbDc+c0p4SlhBJD4BNwU1YU5pDBkFJR98bC1BJwUMGFxVJHFueA84LQAsRlgbORY8CStTBxMoDxkJcHMQNwQ0Lh0MDR9LenBwbGwUIA80BntRPD4keFR5YyEoGB1Lelo9LTRxIh8xGhkJcGJ/UhQk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cystHlZhIDYhOQ08byA9CwwMeAkgPiVaOAY9GGlbJzQheFR5N0hpAx5JIFokJClacystHlZhIDYhOQ08bwA9CwodflNwKSJQcw82DhlJeVsVORs0ER8mHi0ZbDs0KBhbNA00DxEWESQnNzo2KB8YHxkFPw4pbmAUc0p4ERlgNSkneFR5YyAmAxRJBw8xICVAKkh0ShkUcBU2PggsLQdpV1gPNxYjKWA+c0p4Sm1bPz0nMRl5fFNrOhQIOA4jbC1GNkovBUtAOHE+Nxs8b1FlYFhJdloTLSBYMQs7ARkJcDcmNgotKBwnQg5AdjslOCNhIw0qC11RfgInOR08bwAmAxQ4Ixs8JThNc1d4HAIUcHFzMQ95N1M9Ah0HdjslOCNhIw0qC11RfiInORstaVppDxYNdh8+KGxJemBSRxQUssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35XFd9bBh1EUpqStu0xHERFycMEjYaSlhJfio1OD8UPAR4BlxSJH1zHR88Lwc6SlNJBB8nLT5QIEo3BBlGOTY7LEBTbF5piO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IiKykssTDuvzJo+bZiO35tO/Artmksf/IYFVbMzA/eCs2LwY6PhoRGlptbBhVMRl2KFZaJSI2K1MYJRcFDx4dAhsyLiNMe0NSBlZXMT1zCAwtMiEmBhRJa1oSIyJBID46EnUOETU3DAg7aVEMDR8adlVwHiNYP0hxYFVbMzA/eDk8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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-gvOW7vSzsbEz
return Vm.run(__src, { name = 'Build a ring farm/Build Ring A farm', checksum = 703594195, interval = 2, watermark = 'Y2k-gvOW7vSzsbEz', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
